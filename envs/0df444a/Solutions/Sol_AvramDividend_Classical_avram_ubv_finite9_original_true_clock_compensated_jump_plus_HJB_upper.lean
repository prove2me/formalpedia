-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_true_clock_compensated_jump_plus_HJB_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:25:04.950838+00:00
-- url     : https://prove2.me/submissions/d98be3b6-cdab-48c1-b16f-1e3bf16676ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_real_interior_HJB_bridge
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_discounted_true_stopped_generator_L1_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_canonical_clock_stopped_Taylor_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped compensated jump Taylor martingale plus the true stopped
compact generator HJB drift has integrable nonpositive expected total. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hD : IsAdmissibleLe X x C D)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C.toReal)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
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
      let ρ : ℝ≥0 × Ω → ℝ := fun p =>
        if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
      let R : ℝ≥0 × Ω → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (ρ p * (if Y p ∈ Icc (u + δ) v then
            X.generator w (Y p) - q * w (Y p) else 0))
      let Z : Ω → ℝ := fun ω =>
        ((∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
         (∫ t, ∫ z, GWσ ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))) +
        (∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0
          ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal))
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0  := by
  classical
  intro NX K M S MT σ hσ a Y H HS GW GWσ ρ R Z
  let J : Ω → ℝ := fun ω =>
    (∫ p, GWσ ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, GWσ ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal))
  let G : Ω → ℝ := fun ω =>
    ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)
  have hwReal : ContDiffOn ℝ 2 w (Ioo 0 C.toReal) :=
    (avram_ubv_loc6_finitecap_real_interior_HJB_bridge
      X w C hC hFinite hw_smooth q hw_gen hw_grad).1
  have hMean : Integrable J P ∧ (∫ ω, J ω ∂P) = 0 :=
    (avram_ubv_ito_jumps14_original_canonical_clock_stopped_Taylor_mean_zero
      X x D hD.1.1 w C.toReal u v δ hwReal hw_cont hw_neg
      hu hδ hδone huv hv q hq T) σ hσ
  have hDrift : Integrable G P ∧ ∀ ω, G ω ≤ 0 :=
    avram_ubv_finite9_discounted_true_stopped_generator_L1_nonpos
      X x D C hD hC hFinite w hw_smooth hw_cont hw_neg q hq
      hw_gen hw_grad u v δ hu hδ hδone huv hv T σ hσ
  have hGexpect : (∫ ω, G ω ∂P) ≤ 0 :=
    integral_nonpos_of_ae (Filter.Eventually.of_forall hDrift.2)
  change Integrable (fun ω => J ω + G ω) P ∧
    (∫ ω, J ω + G ω ∂P) ≤ 0
  constructor
  · exact hMean.1.add hDrift.1
  · rw [integral_add hMean.1 hDrift.1, hMean.2, zero_add]
    exact hGexpect
