-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_true_clock_negative_generator_tails_auto_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:41:59.854736+00:00
-- url     : https://prove2.me/submissions/8805c178-ca93-4426-9462-c33d272e1f38

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 0) := by
  classical
  intro Y JG
  have hMeas (n : ℕ) :
      Measurable[𝓕.rightCont.predictable]
        (fun p : ℝ≥0 × Ω => ρ p *
          (∫ z in B n, JG (p,z) ∂X.ν)) := by
    have hMark :=
      avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable
        X x D hD w C u v δ hw hw_cont hw_neg
        hu hδ hδone huv hv μ hμ (B n) (hBm n) (hBneg n)
    exact hρm.mul hMark
  exact
    avram_wave6_04_actual_bounded_predictable_weight_generator_negative_tails_on_true_clock
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv T μ hμclock B hBm hBneg hBanti hBempty
      ρ hρm hρ hMeas
