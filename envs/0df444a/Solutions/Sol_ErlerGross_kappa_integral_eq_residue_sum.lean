-- Prove2me | solution 1 for ErlerGross.kappa_integral_eq_residue_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:06:08.107068+00:00
-- url     : https://prove2.me/submissions/b0368bb9-148f-4076-856c-3b7f702c49ec

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_mode_sum_eq_kappa_integral
import Theorems.Thm_ErlerGross_mode_sum_eq_B3

open Real Filter Topology MeasureTheory

theorem solution :
    HasSum (fun n : ℕ => ErlerGross.b3Term (n + 1))
      (∫ κ, ErlerGross.kappaIntegrand κ) := by
  obtain ⟨hsB3, hB3⟩ := ErlerGross.mode_sum_eq_B3
  obtain ⟨_, hκ⟩ := ErlerGross.mode_sum_eq_kappa_integral
  have hvalues := hB3.unique hκ
  have hsum_eq : (∑' n : ℕ, ErlerGross.b3Term (n + 1)) =
      ∫ κ, ErlerGross.kappaIntegrand κ := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
    simpa using hvalues
  simpa only [hsum_eq] using hsB3.hasSum
