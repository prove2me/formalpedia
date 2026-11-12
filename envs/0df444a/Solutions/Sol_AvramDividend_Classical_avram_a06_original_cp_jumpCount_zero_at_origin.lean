-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:56:31.046062+00:00
-- url     : https://prove2.me/submissions/1b98231d-6fbe-4719-83b9-54eb9fd36d82

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- The first original arrival is strictly after time zero almost surely. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ) = 0 := by
  filter_upwards [levy_foundations_compoundDriverInterarrivalPositive
    hd (by norm_num)] with ω hpos
  have hfirst : (0 : ℝ) < LevyFoundations.arrival τ 0 ω := by
    simpa [LevyFoundations.arrival] using hpos 0
  unfold LevyFoundations.jumpCount
  exact Nat.le_zero.mp (Nat.sInf_le
    (show (0 : ℕ) ∈ {n | (0 : ℝ) < LevyFoundations.arrival τ n ω}
      from hfirst))
