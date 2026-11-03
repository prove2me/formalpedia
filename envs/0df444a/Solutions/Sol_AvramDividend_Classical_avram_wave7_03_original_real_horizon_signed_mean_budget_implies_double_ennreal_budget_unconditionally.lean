-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_real_horizon_signed_mean_budget_implies_double_ennreal_budget_unconditionally
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:18:52.796814+00:00
-- url     : https://prove2.me/submissions/eb715069-b9d6-4c15-849c-0d78e98090e8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- At every finite nonnegative real horizon, a budget for the genuine
    original signed expected Stieltjes cash immediately bounds the exact
    double ENNReal expected cash, with no extra integrability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T)
    (B : ℝ)
    (hSignedBudget :
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  let θ : Ω → ℝ≥0 := fun _ => T.toNNReal
  have hCast (ω : Ω) : (θ ω : ℝ) = T :=
    Real.coe_toNNReal T hT
  have hθBound : ∀ ω, θ ω ≤ T.toNNReal := fun _ => le_rfl
  have hEq :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T.toNNReal θ hθBound measurable_const
  have hEqReal :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
      ENNReal.ofReal
        (∫ ω, (∫ t in
            paymentTimes (ruinTime X x D ω) ∩ Iic T,
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
    simpa only [hCast] using hEq
  rw [hEqReal]
  exact ENNReal.ofReal_le_ofReal hSignedBudget
