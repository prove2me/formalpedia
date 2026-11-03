-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_true_clock_HJB_nonpositive_with_negative_generator_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:28:41.73575+00:00
-- url     : https://prove2.me/submissions/d91984e9-662b-4963-826e-5136f1ce89d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 ∧
      Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
        ‖a p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂μ)
        atTop (𝓝 0) := by
  intro Y ρ R JG
  obtain ⟨μ, hμfinite, hμclock, hRint, hRnonpos⟩ :=
    avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv q T hw_gen
  refine ⟨μ, hμfinite, hμclock, hRint, hRnonpos, ?_⟩
  exact avram_wave7_07_true_clock_negative_generator_tail_automatic_predictability
    X x D hD w C u v δ hw hw_cont hw_neg
    hu hδ hδone huv hv T μ hμclock
    B hBm hBneg hBanti hBempty a ham ha
