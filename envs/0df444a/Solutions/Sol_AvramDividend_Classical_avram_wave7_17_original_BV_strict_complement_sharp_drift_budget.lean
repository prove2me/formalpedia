-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:10:27.489758+00:00
-- url     : https://prove2.me/submissions/a6602d7e-e79b-41f5-9839-71e4527daf90

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    0 < T ∧ 0 < X.drift ∧
    0 < (x + T * X.drift - w x) ∧
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
       x + T * X.drift := by
  have hsec := avram_wave3_03_bv_full_cap_gradient_secant
    C hC w hw_cont hw_smooth hw_grad 0 x (le_refl 0) hx hxc
  have hxw : x ≤ w x := by linarith
  have hgap : w x < x + T * X.drift := lt_of_not_ge hEnvelope
  have hTpos : 0 < T := by
    by_contra hn
    have hzero : T = 0 := by linarith [le_of_not_gt hn]
    subst T
    simp only [zero_mul, add_zero] at hgap
    linarith
  have hdpos : 0 < X.drift := by
    by_contra hn
    have hmul : T * X.drift ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hT (le_of_not_gt hn)
    linarith
  have hcash :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
         x + T * X.drift := by
    let tN : ℝ≥0 := ⟨T, hT⟩
    let τ : Ω → ℝ≥0 := fun _ => tN
    have hbound : ∀ ω, τ ω ≤ tN := by intro ω; exact le_rfl
    have hmeas : Measurable (fun ω : Ω => ((τ ω : ℝ≥0) : ℝ)) :=
      measurable_const
    have hb := avram_wave6_chat09_original_bv_sharp_bounded_random_clock_real_cash_mean
      X hX hBV x hx C hxc D hD q (le_of_lt hq)
      tN τ hbound hmeas
    have hc : (tN : ℝ) = T := rfl
    simpa only [τ, hc] using hb
  exact ⟨hTpos, hdpos, by linarith, hcash⟩
