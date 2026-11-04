-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_raw_levy_exponential_expected_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T11:11:20.184179+00:00
-- url     : https://prove2.me/submissions/c1d4455b-82e5-4cf6-b5b6-976566bf08b7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_discounted_exponential_levy_supermartingale
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The real original source discounted exponential has expected value at most one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    (∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * q) ∂P) ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℝ≥0 → Ω → ℝ := fun u ω =>
    Real.exp (θ * X.X u ω - (u : ℝ) * q)
  have hSM : Supermartingale f 𝓕 P :=
    discounted_exponential_levy_supermartingale X θ q hθ hψ
  have hZero : f 0 = fun _ => (1 : ℝ) := by
    funext ω
    simp [f, X.X_zero ω]
  have hBound := hSM.setIntegral_le (by positivity : (0 : ℝ≥0) ≤ t)
    MeasurableSet.univ
  change (∫ ω, f t ω ∂P) ≤ 1
  rw [hZero] at hBound
  simpa using hBound
