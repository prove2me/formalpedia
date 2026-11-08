-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps14_original_stopped_compensated_Taylor_plus_HJB_drift_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:41:43.194408+00:00
-- url     : https://prove2.me/submissions/9e835238-6852-4573-98fa-8691a5e00f0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_canonical_clock_stopped_Taylor_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original centred stopped Taylor compensation plus the pointwise HJB drift sign. -/
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (Ccap : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < Ccap →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      0 < y ∧ ENNReal.ofReal y < Ccap) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    let M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := P.bind K
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
    let MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)) := M.restrict S
    ∀ (σ : Ω → ℝ≥0)
      (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))),
      let a : (ℝ≥0 × Ω) → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
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
      let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
      let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1.1 ≤ σ p.1.2 then GW p else 0
      let B : Ω → ℝ := fun ω =>
        ∫ t : ℝ≥0,
          (if (t, ω) ∈ E then
            (if t ≤ T then Real.exp (-(q * (t : ℝ))) else 0) *
              (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
              (X.generator w (Y (t, ω)) - q * w (Y (t, ω)))
           else 0)
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal)
      Integrable B P →
      Integrable (fun ω =>
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) + B ω) P ∧
      (∫ ω,
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) + B ω ∂P) ≤ 0 := by
  intro NX K M S MT σ hσ a Y H HS GW GWσ B hBI
  let J : Ω → ℝ := fun ω =>
    (∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, GWσ ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))
  have hJump : Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by
    simpa only [J] using
      (avram_ubv_ito_jumps14_original_canonical_clock_stopped_Taylor_mean_zero
        X x D hD w C u v δ hw hw_cont hw_neg
        hu hδ hδone huv hv q hq T σ hσ)
  have hBsign : ∀ ω, B ω ≤ 0 := by
    intro ω
    dsimp only [B]
    apply MeasureTheory.integral_nonpos_of_ae
    refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases hp : (t, ω) ∈ E
    · simp only [if_pos hp]
      have hy := hE (t, ω) hp
      have hgen := (hw_gen _ hy.1 hy.2).2
      have htime : 0 ≤ (if t ≤ T then
          Real.exp (-(q * (t : ℝ))) else (0 : ℝ)) := by
        split_ifs <;> positivity
      have hstop : 0 ≤ (if (t : ℝ≥0∞) ≤ ruinTime X x D ω
          then (1 : ℝ) else 0) := by
        split_ifs <;> norm_num
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg htime hstop) hgen
    · simp only [if_neg hp]
      exact le_rfl
  have hBmean : (∫ ω, B ω ∂P) ≤ 0 :=
    MeasureTheory.integral_nonpos_of_ae
      (Filter.Eventually.of_forall hBsign)
  change Integrable (fun ω => J ω + B ω) P ∧
    (∫ ω, J ω + B ω ∂P) ≤ 0
  constructor
  · exact hJump.1.add hBI
  · rw [MeasureTheory.integral_add hJump.1 hBI, hJump.2]
    simpa using hBmean
