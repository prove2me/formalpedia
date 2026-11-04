-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_generator_finite_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:58:32.769145+00:00
-- url     : https://prove2.me/submissions/594c1119-81a0-4a7d-8881-11ce8e92ad12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped negative-jump generator drift retains L1 under
nonnegative genuine exponential discount on the finite predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (q : ℝ) (hq : 0 ≤ q) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      Real.exp (-(q * (p.1 : ℝ))) * (∫ z in B, G (p,z) ∂X.ν)) μ := by
  classical
  have hBase :=
    avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
      X x C D hD w u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ B hBm hBneg
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hMeas : AEStronglyMeasurable
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) μ :=
    (avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q).aestronglyMeasurable
  have hBound : ∀ᵐ p : ℝ≥0 × Ω ∂μ,
      ‖Real.exp (-(q * (p.1 : ℝ)))‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  exact hBase.bdd_mul hMeas hBound
