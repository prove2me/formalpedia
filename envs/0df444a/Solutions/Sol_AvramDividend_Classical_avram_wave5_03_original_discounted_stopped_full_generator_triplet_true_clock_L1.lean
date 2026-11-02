-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:51:40.303654+00:00
-- url     : https://prove2.me/submissions/e32f2485-31aa-4e76-baa4-51a49f318748

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Discounted source generator triplet is L1 on the exact finite original clock. -/
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0
    let L : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
      else 0
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          ((ρ p * G p + ρ p * L p) +
            (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν))) μ := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
    else 0
  let L : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
    else 0
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  let B : ℝ≥0 → Ω → ℝ := fun t _ => Real.exp (-(q * (t : ℝ)))
  change ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
    μ Set.univ < ⊤ ∧
    (∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    Integrable (fun p : ℝ≥0 × Ω =>
      B p.1 p.2 * ((ρ p * G p + ρ p * L p) +
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν))) μ
  obtain ⟨μ, hμfinite, hμsets, hInt⟩ :=
    avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q T
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hBadapt : StronglyAdapted 𝓕.rightCont B := by
    intro t
    exact stronglyMeasurable_const
  have hBcont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt (fun s => B s ω) (Iic t) t := by
    intro ω t
    dsimp [B]
    fun_prop
  have hBpred : IsStronglyPredictable 𝓕.rightCont B :=
    avram_wave3_04_strongAdapted_leftContinuous_predictable hBadapt hBcont
  have hBbound (p : ℝ≥0 × Ω) : ‖B p.1 p.2‖ ≤ (1 : ℝ) := by
    have ht : 0 ≤ (p.1 : ℝ) := NNReal.coe_nonneg p.1
    have hmul : 0 ≤ q * (p.1 : ℝ) := mul_nonneg hq ht
    have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
    simpa [B, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  have hBae : ∀ᵐ p ∂μ, ‖B p.1 p.2‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall hBbound
  refine ⟨μ, hμfinite, hμsets, ?_⟩
  exact hInt.bdd_mul hBpred.measurable.aestronglyMeasurable hBae
