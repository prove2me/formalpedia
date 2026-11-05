-- Prove2me | solution 7 for AvramDividend.Classical.admissible_cap_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:47:38.700382+00:00
-- url     : https://prove2.me/submissions/b389f26e-fe70-43f1-9d46-92799d05bec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities
import Theorems.Thm_AvramDividend_Classical_verification_candidate_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original BV HJB verification value inequality follows from the
source signed horizon HJB budget and proved exact terminal/cash bridges. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    have h := hjb_component_inequalities X q w C hw_hjb y hy hyC
    exact ⟨h.1, h.2.1⟩
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    exact (hjb_component_inequalities X q w C hw_hjb y hy hyC).2.2
  have hSmooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    exact ⟨fun h => (h hBV).elim, fun _ => hw_smooth⟩
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht htr
    exact verification_candidate_nonneg_before_ruin X q w C
      hw_cont hw0 hSmooth hw_hjb x D hD ω t ht htr
  have hJump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) :=
    avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
      X hX hBV C hC w hw_cont hw_smooth hGrad x hx hxc D hD
  apply avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
    X x C D hD q (le_of_lt hq) (w x)
  intro n
  let T : ℝ := (n + 1 : ℕ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTpos : 0 < T := by dsimp [T]; positivity
  let S : ℝ≥0 := ⟨T, hT⟩
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Signed : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
    else 0
  let Pos : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      max 0 (Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω))
    else 0
  have hStopped := avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGen
    hGrad x hx hxc D hD hNonneg hJump T hT hTpos
  change (∫ ω, Cash ω ∂P) + (∫ ω, Signed ω ∂P) ≤ w x at hStopped
  have hTerminal := avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
    X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hGrad
    x D hD T hT hTpos
  have hTermMeanEq : (∫ ω, Signed ω ∂P) = (∫ ω, Pos ω ∂P) := hTerminal.2
  have hPosMean : 0 ≤ ∫ ω, Pos ω ∂P :=
    avram_wave8_20_original_strict_survival_terminal_expectation_nonnegative
      X x D w q S
  have hSignedMeanNonneg : 0 ≤ ∫ ω, Signed ω ∂P := by
    rw [hTermMeanEq]
    exact hPosMean
  have hCashMean : (∫ ω, Cash ω ∂P) ≤ w x := by
    linarith [hStopped, hSignedMeanNonneg]
  have hRealEq := avram_wave7_03_original_real_toReal_cash_mean_eq_signed_stieltjes_mean
    X x C D hD q (le_of_lt hq) T hT
  calc
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((n + 1 : ℕ) : ℝ)),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) =
        (∫ ω, Cash ω ∂P) := hRealEq.symm
    _ ≤ w x := hCashMean