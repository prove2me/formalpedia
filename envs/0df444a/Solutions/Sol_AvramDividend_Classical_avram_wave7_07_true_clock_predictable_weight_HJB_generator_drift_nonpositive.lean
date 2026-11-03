-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_true_clock_predictable_weight_HJB_generator_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:39:36.178059+00:00
-- url     : https://prove2.me/submissions/f09603d9-3582-4df4-b8a3-a4f531f2234e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded predictable weights preserve the original stopped full-source
HJB generator drift L1 integrability and its nonpositive expectation. -/
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
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p => a p * R p) μ ∧
      (∫ p, a p * R p ∂μ) ≤ 0 := by
  classical
  intro Y ρ R
  obtain ⟨μ, hμfinite, hμclock, hRint, _⟩ :=
    avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q T hw_gen
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hBound : ∀ᵐ p : ℝ≥0 × Ω ∂μ, ‖a p‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(ha p).1], (ha p).2⟩
  have hWeightedInt : Integrable (fun p => a p * R p) μ :=
    hRint.bdd_mul ham.aestronglyMeasurable hBound
  have hRnonpos (p : ℝ≥0 × Ω) : R p ≤ 0 := by
    by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · by_cases hb : Y p ∈ Icc (u + δ) v
      · have hypos : 0 < Y p := lt_of_lt_of_le (add_pos hu hδ) hb.1
        have hylt : Y p < C := lt_of_le_of_lt hb.2 hv
        have hres : X.generator w (Y p) - q * w (Y p) ≤ 0 :=
          (hw_gen (Y p) hypos hylt).2
        simpa only [R, ρ, if_pos hs, if_pos hb, one_mul, Pi.zero_apply]
          using hres
      · simp only [R, ρ, if_pos hs, if_neg hb, one_mul]
        exact le_refl 0
    · simp only [R, ρ, if_neg hs, zero_mul]
      exact le_refl 0
  refine ⟨μ, hμfinite, hμclock, hWeightedInt, ?_⟩
  apply integral_nonpos_of_ae
  exact Filter.Eventually.of_forall (fun p =>
    mul_nonpos_of_nonneg_of_nonpos (ha p).1 (hRnonpos p))
