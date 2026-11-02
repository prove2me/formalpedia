-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_discounted_true_clock_compact_generator_hjb_L1_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:03:34.388226+00:00
-- url     : https://prove2.me/submissions/7d84862d-c030-4d02-b423-641b858f8e6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Full discounted original source stopped generator HJB is L1 and nonpositive. -/
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (ρ p * (if Y p ∈ Icc (u + δ) v then
          X.generator w (Y p) - q * w (Y p) else 0))
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let R : ℝ≥0 × Ω → ℝ := fun p =>
    Real.exp (-(q * (p.1 : ℝ))) *
      (ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0))
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
    else 0
  let L : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
    else 0
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
    μ Set.univ < ⊤ ∧
    (∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    Integrable R μ ∧ (∫ p, R p ∂μ) ≤ 0
  obtain ⟨μ, hμfinite, hμsets, hInt⟩ :=
    avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T
  have hBaseEq : ∀ p : ℝ≥0 × Ω,
      (ρ p * G p + ρ p * L p) +
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0) := by
    simpa only [G, L, JG, Y, ρ] using
      (avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
        X x D w u v δ q)
  have hEq : ∀ p : ℝ≥0 × Ω,
      Real.exp (-(q * (p.1 : ℝ))) *
        ((ρ p * G p + ρ p * L p) +
          (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) = R p := by
    intro p
    rw [hBaseEq p]
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hRint : Integrable R μ := hInt.congr (Filter.Eventually.of_forall hEq)
  refine ⟨μ, hμfinite, hμsets, hRint, ?_⟩
  apply MeasureTheory.integral_nonpos_of_ae
  apply Filter.Eventually.of_forall
  intro p
  by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
  · by_cases hb : Y p ∈ Icc (u + δ) v
    · have hypos : 0 < Y p := lt_of_lt_of_le (add_pos hu hδ) hb.1
      have hylt : Y p < C := lt_of_le_of_lt hb.2 hv
      have hres : X.generator w (Y p) - q * w (Y p) ≤ 0 :=
        (hw_gen (Y p) hypos hylt).2
      have he : 0 ≤ Real.exp (-(q * (p.1 : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      simpa only [R, ρ, if_pos hs, if_pos hb, one_mul, Pi.zero_apply] using
        (mul_nonpos_of_nonneg_of_nonpos he hres)
    · simp only [R, ρ, if_pos hs, if_neg hb, one_mul, mul_zero]
      exact le_refl 0
  · simp only [R, ρ, if_neg hs, zero_mul, mul_zero]
    exact le_refl 0
