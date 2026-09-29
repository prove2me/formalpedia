-- Prove2me | solution 1 for CubicP3Partition.six_dvd_order_band_candidate
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:54:34.401532+00:00
-- url     : https://prove2.me/submissions/fb0a34f1-569d-45ed-a40a-36e9cea37bcb

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition


end CubicP3Partition

open CubicP3Partition
theorem solution
    {n : Nat} (hSix : 6 ∣ n) (hMin : 4 ≤ n) :
    n = 6 ∨ n = 12 ∨ 18 ≤ n := by
  rcases hSix with ⟨k, hk⟩
  omega

