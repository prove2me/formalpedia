-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_expected_le_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:54:11.887188+00:00
-- url     : https://prove2.me/submissions/a48ba461-9ea8-4861-8a23-56d57b5e6e1c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original controlled exponential expectation does not exceed initial capital exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    (∫ ω, Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q) ∂P) ≤
    Real.exp (θ * x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℝ≥0 → Ω → ℝ :=
    fun u ω => Real.exp
      (θ * (x + X.X u ω - rightLimit D u ω) - (u : ℝ) * q)
  have hSM : Supermartingale f 𝓕.rightCont P :=
    avram_wave4_03_postPayment_discounted_exponential_supermartingale
      X x D hD θ q hθ hψ
  have hFzero : ∀ ω, f 0 ω ≤ Real.exp (θ * x) := by
    intro ω
    have hD0 : 0 ≤ rightLimit D 0 ω :=
      le_trans
        (dividendStrategy_path_nonneg D hD ω 0)
        (dividendStrategy_le_rightLimit D hD ω 0)
    have hArg :
        θ * (x + X.X 0 ω - rightLimit D 0 ω) -
          ((0 : ℝ≥0) : ℝ) * q ≤ θ * x := by
      simp only [X.X_zero ω, NNReal.coe_zero, zero_mul, sub_zero]
      nlinarith [mul_nonneg hθ hD0]
    exact Real.exp_le_exp.mpr hArg
  have hFirst : (∫ ω, f t ω ∂P) ≤ (∫ ω, f 0 ω ∂P) := by
    simpa using (hSM.setIntegral_le (by positivity : (0 : ℝ≥0) ≤ t)
      MeasurableSet.univ)
  have hSecond : (∫ ω, f 0 ω ∂P) ≤ Real.exp (θ * x) := by
    calc
      (∫ ω, f 0 ω ∂P) ≤
          (∫ _ω, Real.exp (θ * x) ∂P) := by
        apply integral_mono_ae (hSM.integrable 0)
          (integrable_const (Real.exp (θ * x)))
        exact Filter.Eventually.of_forall hFzero
      _ = Real.exp (θ * x) := by simp
  exact le_trans hFirst hSecond
