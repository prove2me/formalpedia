-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_finite_window_signed_HJB_from_C1_compact_localization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:49:38.737146+00:00
-- url     : https://prove2.me/submissions/9695ba26-6d99-4144-bd6f-003b8161e750

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_finite_window_signed_generator_stieltjes_HJB_with_bounded_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
/-- Exact BV signed physical generator plus real Stieltjes HJB local budget follows from C1 compact localization, with K and clock positivity derived. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, 0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (F : (ℝ≥0 × Ω) → ℝ)
    (hF : ∀ p ∈ E, F p =
      Real.exp (-(q * (p.1 : ℝ))) *
      (X.generator w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)))
    (hFI : IntegrableOn F E μ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (T : ℝ≥0)
    (hAwindow : A ⊆ paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ))
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hReserveBand : ∀ t ∈ A, riskProcess X x D t.toNNReal ω ∈ Icc a b)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      ((dividendMeasure D ω).restrict A)) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∫ p in E, F p ∂μ) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω))
        ∂(dividendMeasure D ω)) ≤ w x := by
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  obtain ⟨K, hK⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((hw_smooth.continuousOn_deriv_of_isOpen hOpen
        (by norm_num)).mono hBand)
  have hDerivBound : ∀ t ∈ A,
      |deriv w (riskProcess X x D t.toNNReal ω)| ≤ |K| := by
    intro t ht
    have hNorm :
        ‖deriv w (riskProcess X x D t.toNNReal ω)‖ ≤ K :=
      hK _ (hReserveBand t ht)
    simpa only [Real.norm_eq_abs] using hNorm.trans (le_abs_self K)
  have hApos : ∀ t ∈ A, 0 ≤ t := by
    intro t ht
    exact (paymentTimes_membership_to_nNReal_active
      (ruinTime X x D ω) t (hAwindow ht).1).1
  exact
    avram_wave7_02_original_BV_finite_window_signed_generator_stieltjes_HJB_with_bounded_gradient
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth
      hw_gen hw_grad x hx hxc D hD ω μ E hEm hEregion
      F hF hFI A hAm hAregion T hAwindow hApos
      |K| (abs_nonneg K) hDerivBound hMeas
