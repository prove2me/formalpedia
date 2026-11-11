-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_compoundPoisson_exp_ae_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:08:59.671673+00:00
-- url     : https://prove2.me/submissions/dc276c30-47ae-46fb-9e9c-d049657b63c2

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoisson_path_le_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

/-- All nonnegative Laplace exponentials of the original negative-mark source are
simultaneously bounded by the deterministic drift exponential almost surely. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {P : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ᵐ ω ∂P, ∀ t θ : ℝ, 0 ≤ θ →
      Real.exp (θ * LevyFoundations.compoundPoisson (1 : ℝ) τ Y t ω) ≤
        Real.exp (θ * t) := by
  filter_upwards [AvramDividend.Classical.avram_a06_compound_driver_all_marks_negative hd]
    with ω hneg
  intro t θ hθ
  have hb := AvramDividend.Classical.avram_a06_compoundPoisson_path_le_drift
    (1 : ℝ) τ Y ω (fun n => le_of_lt (hneg n)) t
  exact Real.exp_le_exp.mpr (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_left hb hθ)
