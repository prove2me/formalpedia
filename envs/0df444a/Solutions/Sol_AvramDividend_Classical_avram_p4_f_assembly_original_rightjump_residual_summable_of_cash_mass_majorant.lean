-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightjump_residual_summable_of_cash_mass_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:34:52.097197+00:00
-- url     : https://prove2.me/submissions/698dee8c-36d9-4eda-8339-38742306d4a4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every norm-dominated original signed residual is summable from Cash jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (A : Set ℝ≥0)
    (R : A → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hCash : Summable (fun a : A =>
      rightLimit D a.1 ω - D a.1 ω))
    (hMajor : ∀ a : A, ‖R a‖ ≤
      K * (rightLimit D a.1 ω - D a.1 ω)) :
    Summable R := by
  have hControl : Summable (fun a : A =>
      K * (rightLimit D a.1 ω - D a.1 ω)) :=
    hCash.mul_left K
  exact hControl.of_norm_bounded hMajor

