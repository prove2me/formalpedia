-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_route11_canonical_zero_cap_hypotheses_refute
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:11:51.120583+00:00
-- url     : https://prove2.me/submissions/932a1559-b400-4152-a22e-1dd4ca7e5a10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_contact_positive_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- All original core premises at zero cap yield a false cash upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ¬ ∀ (w : ℝ → ℝ) (C : ℝ≥0∞)
        (hw_cont : ContinuousOn w (Ici 0))
        (hw_neg : ∀ y < 0, w y = 0)
        (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
        (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
        (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
        (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
        (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω))
        (hjump : ∀ ω (t : ℝ≥0),
          (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
        (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
  classical
  intro hAll
  obtain ⟨n, hD, hRight, hPos⟩ :=
    avram_bv_route11_zero_cap_contact_positive_cash X hX hBV hFinite q hq
  have hSmooth : ContDiffOn ℝ 1 (fun _ : ℝ => (0 : ℝ))
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < (0 : ℝ≥0∞)} := by
    exact contDiffOn_const
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (0 : ℝ≥0∞) →
      X.GeneratorIntegrable (fun _ => (0 : ℝ)) y ∧
        X.generator (fun _ => (0 : ℝ)) y - q * (0 : ℝ) ≤ 0 := by
    intro y _ hy
    exact (not_lt_of_ge bot_le hy).elim
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < (0 : ℝ≥0∞) →
      1 ≤ deriv (fun _ : ℝ => (0 : ℝ)) y := by
    intro y _ hy
    exact (not_lt_of_ge bot_le hy).elim
  have hJump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 (barrierStrategy X 0 0) ω) →
      rightLimit (barrierStrategy X 0 0) t ω - barrierStrategy X 0 0 t ω ≤
        (fun _ : ℝ => (0 : ℝ)) (riskProcess X 0 (barrierStrategy X 0 0) t ω) -
          (fun _ : ℝ => (0 : ℝ))
            (riskProcess X 0 (barrierStrategy X 0 0) t ω -
              (rightLimit (barrierStrategy X 0 0) t ω -
                barrierStrategy X 0 0 t ω)) := by
    intro ω t ht
    simp [hRight ω t ht]
  have hBudget := hAll (fun _ : ℝ => (0 : ℝ)) (0 : ℝ≥0∞)
    (by fun_prop) (by simp) hSmooth hGen hGrad
    0 (by simp) (barrierStrategy X 0 0) hD
    (by intro ω t ht hr; simp) hJump (n : ℝ) (by positivity)
  exact (not_le_of_gt hPos) (by simpa using hBudget)
