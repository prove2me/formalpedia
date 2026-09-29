-- Prove2me | solution 2 for ErlerGross.mode_sum_eq_B3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:07:52.511919+00:00
-- url     : https://prove2.me/submissions/e87088ce-d2a0-472e-af7a-5d6299dbd356

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_mode_sum_eq_kappa_integral
import Theorems.Thm_ErlerGross_kappa_integral_eq_residue_sum

open Real Filter Topology MeasureTheory ErlerGross

theorem solution :
    Summable (fun n : ℕ => b3Term (n + 1)) ∧
      HasSum (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
        (2 * ∑' n : ℕ, b3Term (n + 1)) := by
  rcases ErlerGross.mode_sum_eq_kappa_integral with ⟨_, hmode⟩
  have hres := ErlerGross.kappa_integral_eq_residue_sum
  refine ⟨hres.summable, ?_⟩
  rw [hres.tsum_eq]
  exact hmode