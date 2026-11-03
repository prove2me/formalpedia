-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_discounted_stopped_negative_taylor_product_eq_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:31:33.890386+00:00
-- url     : https://prove2.me/submissions/21c12995-e1f1-46d0-ab9c-959d36cc1c75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-faithful nonnegative-discount signed C2 negative-jump compensator
on a finite predictable clock. Predictability of discount is explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (q : ℝ) (hq : 0 ≤ q)
    (hdisc : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∫ r : ((ℝ≥0 × Ω) × ℝ),
      Real.exp (-(q * (r.1.1 : ℝ))) * HS r
      ∂(letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
        μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
    (∫ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in Iio (0 : ℝ), G (p,z) ∂X.ν) ∂μ) := by
  classical
  intro Y H HS G
  have hBound (p : ℝ≥0 × Ω) :
      |Real.exp (-(q * (p.1 : ℝ)))| ≤ 1 := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  have hInt :=
    avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ (Set.univ : Set ((ℝ≥0 × Ω) × ℝ))
      MeasurableSet.univ
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
      hdisc hBound
  have hFub :=
    avram_wave7_07_original_signed_predictable_negative_generator_fubini_of_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ (Set.univ : Set ((ℝ≥0 × Ω) × ℝ))
      MeasurableSet.univ
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
      hdisc hBound hInt
  have hGenerator :=
    avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ (Set.univ : Set ((ℝ≥0 × Ω) × ℝ))
      MeasurableSet.univ
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
      hdisc hBound
  have hCore := hFub.trans hGenerator.2
  simpa only [Set.indicator_univ] using hCore