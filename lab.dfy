method BinarySearch(arr: array<int>, key: int) returns (index: int)
    requires forall i :: 0 <= i < arr.Length-1 ==> arr[i] <= arr[i+1] 
    ensures index == -1 || (0 <= index < arr.Length && arr[index] == key) 
{
    var low := 0;
    var high := arr.Length - 1;
    index := -1; 

    while low <= high
        invariant 0 <= low <= high + 1 <= arr.Length
    {
        var mid := low + (high - low) / 2;
        if arr[mid] == key {
            index := mid;
            return;
        } else if arr[mid] < key {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
}
