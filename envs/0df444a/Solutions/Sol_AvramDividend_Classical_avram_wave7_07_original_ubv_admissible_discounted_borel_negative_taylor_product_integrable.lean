-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_borel_negative_taylor_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:00:13.429341+00:00
-- url     : https://prove2.me/submissions/96458032-246b-4b1c-9371-d46c03035e9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original UBV admissible discounted C2 Taylor correction is Bochner L1
on the true predictable-time × original negative Lévy mark measure. -/
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
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {r | r.2 ∈ B}
    Integrable (fun r : ((ℝ≥0 × Ω) × ℝ) =>
      (S.indicator (fun r => Real.exp (-(q * (r.1.1 : ℝ))) * HS r)) r) (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  classical
  intro Y H HS S
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨R, hvR, _, hwR⟩ :=
    avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists w C v hv0 hv hw
  have hS :
      MeasurableSet[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)] S := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    exact hBm.preimage measurable_snd
  have hBound (p : ℝ≥0 × Ω) :
      |Real.exp (-(q * (p.1 : ℝ)))| ≤ 1 := by
    rw [abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  exact avram_wave7_07_original_signed_predictable_negative_taylor_product_integrable
    X x D hD.1.1 w R u v δ hwR hw_cont hw_neg
    hu hδ hδone huv hvR μ hμ S hS
    (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
    (avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q) hBound
