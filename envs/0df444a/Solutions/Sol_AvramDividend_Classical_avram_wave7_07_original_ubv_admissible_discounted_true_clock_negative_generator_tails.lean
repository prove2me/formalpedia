-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_discounted_true_clock_negative_generator_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:19:33.58493+00:00
-- url     : https://prove2.me/submissions/16d37f63-115b-41eb-9303-44fa4e4f6b9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_ubv_extended_cap_true_clock_negative_generator_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_time_exponential_discount_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original UBV admissible true-clock negative Lévy mark tails vanish
under the genuine predictable exponential discount. -/
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
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (q : ℝ) (hq : 0 ≤ q) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (∀ n, Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) *
        (∫ z in B n, JG (p,z) ∂X.ν))) →
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖Real.exp (-(q * (p.1 : ℝ))) * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by
  classical
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨R, hvR, hRC, _⟩ :=
    avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists w C v hv0 hv hw
  have hWeight (p : ℝ≥0 × Ω) :
      0 ≤ Real.exp (-(q * (p.1 : ℝ))) ∧
      Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
    constructor
    · exact Real.exp_nonneg _
    · apply Real.exp_le_one_iff.mpr
      have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg _
      exact neg_nonpos.mpr (mul_nonneg hq ht)
  exact avram_wave7_07_original_ubv_extended_cap_true_clock_negative_generator_tails
    X x D hD.1.1 w C R u v δ hw hw_cont hw_neg
    hu hδ hδone huv hvR hRC T μ hμclock
    B hBm hBneg hBanti hBempty
    (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))))
    (avram_wave7_07_original_predictable_time_exponential_discount_measurable
      (𝓕 := 𝓕) q) hWeight
