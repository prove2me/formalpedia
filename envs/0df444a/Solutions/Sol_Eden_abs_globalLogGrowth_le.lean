-- Prove2me | solution 1 for Eden.abs_globalLogGrowth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:01.125892+00:00
-- url     : https://prove2.me/submissions/832e7c1a-38d2-4a3f-aa17-5b166841cfcc

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_globalLogGrowth_bounds

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) : |globalLogGrowth c k t| ≤ ((k : ℝ) * c) * t := by
  have h := globalLogGrowth_bounds hk hc ht
  have hkt : 0 ≤ (k : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
  rw [abs_le]
  constructor <;> nlinarith
end Eden
