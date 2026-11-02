-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:49:26.682554+00:00
-- url     : https://prove2.me/submissions/03a39813-72b7-4fa8-bedc-a926f7e1a3be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original stopped C² source Taylor measure admits bounded measurable
time weights without any new dividend independence or fibre-integrability
hypothesis. The source jump times and marks remain those of the original X. -/
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
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0)
    (a : ℝ≥0 → ℝ) (ha : Measurable a)
    (M : ℝ) (ha_bound : ∀ r : ℝ≥0, |a r| ≤ M) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    let GW : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
        a p.1 * HS ((p.1,ω),p.2) else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable GW (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, GW p ∂NX ω) =
        ∑ r ∈ T, a r * HS ((r,ω),J r ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun r η =>
    X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
    ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
      (fun r : ℝ≥0 => (r, J r η)))
  let G : ℝ≥0 × ℝ → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
  let GW : ℝ≥0 × ℝ → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
      a p.1 * HS ((p.1,ω),p.2) else 0
  change ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable GW (NX ω) ∧
      (∫ p : ℝ≥0 × ℝ, GW p ∂NX ω) =
        ∑ r ∈ T, a r * HS ((r,ω),J r ω)
  obtain ⟨T, hT, hInt, _⟩ :=
    avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      s t ω B hBm hBneg ε hε hBsep
  have hweight : Measurable (fun p : ℝ≥0 × ℝ => a p.1) :=
    ha.comp measurable_fst
  have hbound : ∀ᵐ p : ℝ≥0 × ℝ ∂NX ω, ‖a p.1‖ ≤ M :=
    Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using ha_bound p.1)
  have hWeighted : Integrable (fun p : ℝ≥0 × ℝ => a p.1 * G p) (NX ω) :=
    hInt.bdd_mul hweight.aestronglyMeasurable hbound
  have hIntW : Integrable GW (NX ω) := by
    simpa only [G, GW, mul_ite, mul_zero] using hWeighted
  have hμ : (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) Set.univ < ⊤ := by simp
  have hHS : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS := by
    simpa [HS, H, Y] using
      (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        (0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) hμ).1
  have hPredLeProd :
      (𝓕.rightCont.predictable) ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    measurableSpace_le_predictable_of_measurableSet
      (fun A hA => (measurableSet_singleton (⊥ : ℝ≥0)).prod ((𝓕.rightCont.le ⊥) A hA))
      (fun i A hA => measurableSet_Ioi.prod ((𝓕.rightCont.le i) A hA))
  have hHSStd : Measurable HS := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
    exact hHS.mono
      (sup_le_sup (MeasurableSpace.comap_mono hPredLeProd) le_rfl) le_rfl
  have hf : Measurable (fun p : ℝ≥0 × ℝ =>
      a p.1 * HS ((p.1,ω),p.2)) :=
    hweight.mul
      (hHSStd.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
  refine ⟨T, hT, hIntW, ?_⟩
  simpa only [GW, J, NX] using
    (avram_wave5_03_original_intrinsic_signed_finite_band_integral_eq_actual_jump_sum
      X ω s t B hBm hBneg T hT
      (fun p : ℝ≥0 × ℝ => a p.1 * HS ((p.1,ω),p.2)) hf hIntW)
