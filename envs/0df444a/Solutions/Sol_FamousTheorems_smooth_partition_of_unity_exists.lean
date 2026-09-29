-- Prove2me | solution 1 for FamousTheorems.smooth_partition_of_unity_exists
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:45.78952+00:00
-- url     : https://prove2.me/submissions/c2034e7a-f9c1-4189-b58a-5bb4beb725b0

import Mathlib

open scoped ContDiff

theorem solution {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U :=
  SmoothPartitionOfUnity.exists_isSubordinate I hs U ho hU
