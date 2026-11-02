-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:20:25.05131+00:00
-- url     : https://prove2.me/submissions/1fa83a8c-037a-405a-929e-511c072be731

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original stopped full-Stieltjes reward at an arbitrary nonnegative
REAL horizon, including the original time-zero payment, is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp
      (|X.ψ 1 - q| * (((T.toNNReal + 1 : ℝ≥0) : ℝ)))) *
      ENNReal.ofReal (Real.exp x) := by
  let U : ℝ≥0 := T.toNNReal + 1
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hTU : T ≤ (U : ℝ) := by
    simp only [U, NNReal.coe_add, NNReal.coe_one,
      Real.coe_toNNReal T hT]
    linarith
  let wq : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (-(q * s)))
  let E₁ : Ω → Set ℝ := fun ω =>
    paymentTimes (ruinTime X x D ω) ∩ Iic T
  let E₂ : Ω → Set ℝ := fun ω =>
    paymentTimes (ruinTime X x D ω) ∩ Iic (U : ℝ)
  have hE₁ (ω : Ω) : MeasurableSet (E₁ ω) :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iic
  have hE₂ (ω : Ω) : MeasurableSet (E₂ ω) :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iic
  have hsubset (ω : Ω) : E₁ ω ⊆ E₂ ω := by
    intro s hs
    exact ⟨hs.1, le_trans hs.2 hTU⟩
  have hInner (ω : Ω) :
      (∫⁻ s in E₁ ω, wq s ∂(dividendMeasure D ω)) ≤
      (∫⁻ s in E₂ ω, wq s ∂(dividendMeasure D ω)) := by
    have hPoint : (E₁ ω).indicator wq ≤ (E₂ ω).indicator wq := by
      intro s
      by_cases hs : s ∈ E₁ ω
      · have hs₂ : s ∈ E₂ ω := hsubset ω hs
        simp [Set.indicator, hs, hs₂]
      · simp [Set.indicator, hs]
    calc
      (∫⁻ s in E₁ ω, wq s ∂(dividendMeasure D ω)) =
          (∫⁻ s, (E₁ ω).indicator wq s ∂(dividendMeasure D ω)) :=
        (lintegral_indicator (hE₁ ω) wq).symm
      _ ≤ (∫⁻ s, (E₂ ω).indicator wq s ∂(dividendMeasure D ω)) :=
        lintegral_mono hPoint
      _ = (∫⁻ s in E₂ ω, wq s ∂(dividendMeasure D ω)) :=
        lintegral_indicator (hE₂ ω) wq
  have hMoment :=
    avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
      X x C D hD U hU q
  change (∫⁻ ω, ∫⁻ s in E₁ ω, wq s
    ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp
      (|X.ψ 1 - q| * (U : ℝ))) *
        ENNReal.ofReal (Real.exp x)
  calc
    _ ≤ (∫⁻ ω, ∫⁻ s in E₂ ω, wq s
        ∂(dividendMeasure D ω) ∂P) :=
      lintegral_mono hInner
    _ ≤ _ := hMoment
