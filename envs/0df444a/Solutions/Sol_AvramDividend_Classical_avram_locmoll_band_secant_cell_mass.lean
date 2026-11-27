-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_secant_cell_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:41:21.943202+00:00
-- url     : https://prove2.me/submissions/3943e259-e240-4e41-9f94-c172f9c33fe1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    (g : ℝ → ℝ) (a b : ℝ) :
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    Q a b * (a - b) = g a - g b := by 
  dsimp only
  by_cases he : a = b
  · subst b
    simp
  · rw [if_neg he, div_mul_cancel₀ _ (sub_ne_zero.mpr he)]
