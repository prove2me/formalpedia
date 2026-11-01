-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:33:35.25022+00:00
-- url     : https://prove2.me/submissions/402a357e-e248-439d-9b73-ab47d902796c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source theta-scaled exponential martingale consumes the entire
closed-horizon random Stieltjes dividend measure, including t=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
        ∂dividendMeasure D ω ∂P) ≤ 1 := by
  classical
  let f : Ω → ℝ → ℝ≥0∞ := fun ω s =>
    ENNReal.ofReal (θ * Real.exp (θ *
      (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
      (s.toNNReal : ℝ) * X.ψ θ))
  let A : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω)
  let B : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then f ω s
      else 0 ∂dividendMeasure D ω
  have hD0meas : Measurable (rightLimit D (0 : ℝ≥0)) :=
    (dividendStrategy_rightLimit_adapted_rightCont D hD 0).mono
      (𝓕.rightCont.le 0) le_rfl
  have hAmeas : Measurable A := by
    exact (Measurable.mul
      (Measurable.mul measurable_const
        ((hD0meas.const_mul θ).neg.exp)) hD0meas).ennreal_ofReal
  have hzero (ω : Ω) :
      ENNReal.ofReal (rightLimit D 0 ω) * f ω 0 = A ω := by
    dsimp [f, A]
    simp only [Real.toNNReal_zero, X.X_zero ω, zero_sub,
      max_self, zero_mul, sub_zero]
    have hh : θ * (-rightLimit D 0 ω) =
        -(θ * rightLimit D 0 ω) := by ring
    rw [hh]
    rw [ENNReal.ofReal_mul (mul_nonneg (le_of_lt hθ) (Real.exp_nonneg _))]
    ac_rfl
  have hsplit (ω : Ω) :
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        f ω s ∂dividendMeasure D ω) = A ω + B ω := by
    calc
      _ = ENNReal.ofReal (rightLimit D 0 ω) * f ω 0 +
          (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), f ω s ∂dividendMeasure D ω) :=
        avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
          D hD ω T (f ω)
      _ = A ω + B ω := by
        rw [hzero]
        dsimp only [B]
        rw [← lintegral_indicator measurableSet_Ioc (f ω)]
        simp only [Set.indicator_apply]
  have hbudget :=
    avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
      X D hD θ hθ T hT
  have hbudget' :
      (∫⁻ ω, A ω ∂P) + (∫⁻ ω, B ω ∂P) ≤ 1 := by
    simpa only [A, B, f] using hbudget
  calc
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      f ω s ∂dividendMeasure D ω ∂P) =
        (∫⁻ ω, A ω + B ω ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hsplit ω
    _ = (∫⁻ ω, A ω ∂P) + (∫⁻ ω, B ω ∂P) := by
      rw [lintegral_add_left hAmeas]
    _ ≤ 1 := hbudget'
