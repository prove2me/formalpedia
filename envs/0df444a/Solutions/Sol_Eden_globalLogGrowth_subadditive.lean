-- Prove2me | solution 1 for Eden.globalLogGrowth_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:16.205736+00:00
-- url     : https://prove2.me/submissions/ac362718-ab53-45b1-971f-cac355acc1f1

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_supremumSingularProduct_pos
import Theorems.Thm_Eden_supremumSingularProduct_add_le

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c s t : ℝ}
    (hc : 4 ≤ c) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    globalLogGrowth c k (s + t) ≤ globalLogGrowth c k s + globalLogGrowth c k t := by
  have h := Real.log_le_log (supremumSingularProduct_pos hk hc (add_nonneg hs ht))
    (supremumSingularProduct_add_le hk hc hs ht)
  rw [Real.log_mul (ne_of_gt (supremumSingularProduct_pos hk hc hs))
    (ne_of_gt (supremumSingularProduct_pos hk hc ht))] at h
  exact h
end Eden
