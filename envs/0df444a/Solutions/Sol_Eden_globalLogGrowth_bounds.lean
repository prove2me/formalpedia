-- Prove2me | solution 1 for Eden.globalLogGrowth_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:59:37.535778+00:00
-- url     : https://prove2.me/submissions/0f024e29-0b19-41a5-9135-9b6c5a1bdcde

import Definitions.Def_Eden_IntegerGrowthBounds
import Definitions.Def_Eden_GlobalGrowth
import Theorems.Thm_Eden_supremumSingularProduct_bounds
import Theorems.Thm_Eden_supremumSingularProduct_pos

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5) {c t : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) :
    (k : ℝ) * (-c * t) ≤ globalLogGrowth c k t ∧ globalLogGrowth c k t ≤ (k : ℝ) * (3 * t) := by
  have hp := supremumSingularProduct_bounds hk hc ht
  have hl := Real.log_le_log (Real.exp_pos _) hp.1
  have hu := Real.log_le_log (supremumSingularProduct_pos hk hc ht) hp.2
  rw [Real.log_exp] at hl hu
  exact ⟨hl, hu⟩
end Eden
