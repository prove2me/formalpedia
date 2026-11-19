-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward70_original_finiteband_predictable_stopped_Campbell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:21:19.686211+00:00
-- url     : https://prove2.me/submissions/5c832df3-e6a6-4db0-8d62-80febce6ce71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_stopped_signed_L1_physical_clock_autofinite
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite
set_option pp.universes true

set_option pp.explicit true
set_option pp.fullNames true
open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (hBNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤)
    (F : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] F)
    (hSupport : ∀ p, (T < p.1.1 ∨ p.2 ∉ B) → F p = 0)
    (C : ℝ) (hC : 0 ≤ C) (hBound : ∀ p, |F p| ≤ C)
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
  (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
   let μT : Measure ℝ≥0 :=
     ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
   let Z : Ω → ℝ := fun ω =>
     (∫ p, (if p.1 ≤ σ ω then F ((p.1, ω), p.2) else 0) ∂(NX ω)) -
     (∫ t, ∫ z, (if t ≤ σ ω then F ((t, ω), z) else 0)
       ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
   Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  letI : SigmaFinite X.ν :=
    avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let μT : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  obtain ⟨μ, hμfinite, hμclock, _⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧
      X.X t ω - Function.leftLim (fun s => X.X s ω) t ≠ 0}).map
      (fun t => (t, X.X t ω - Function.leftLim (fun s => X.X s ω) t)))
  let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
    fun ω => @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p => ((p.1, ω), p.2)) (NX ω)
  let M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
    P.bind K
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
  let MT := M.restrict S
  let N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) :=
    μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  have hSm :
      MeasurableSet[(@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S :=
    avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable 𝓕 T
  have hνB : (X.ν.restrict (Iio (0 : ℝ))) B < ⊤ := by
    rw [Measure.restrict_apply hB]
    have hInt : B ∩ Iio (0 : ℝ) = B := Set.inter_eq_left.mpr hBNeg
    rw [hInt]
    exact hν
  have hNmass : N ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) < ⊤ := by
    dsimp only [N]
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hμfinite hνB
  have hFint : Integrable F N := by
    have hOn : IntegrableOn F ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) N :=
      N.integrableOn_of_bounded (ne_of_lt hNmass)
        hFm.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => by
          simpa only [Real.norm_eq_abs] using hBound p))
    apply hOn.integrable_of_forall_notMem_eq_zero
    intro p hp
    exact hSupport p (Or.inr (by
      intro hz
      apply hp
      exact ⟨Set.mem_univ _, hz⟩))
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞) then F p else 0
  have hHsup : S.indicator H = H := by
    funext p
    by_cases hp : p ∈ S
    · simp [Set.indicator, hp]
    · have ht : T < p.1.1 := lt_of_not_ge (by simpa [S] using hp)
      have hFzero : F p = 0 := hSupport p (Or.inl ht)
      simp [Set.indicator, hp, H, hFzero]
  have hRes :=
    avram_p2_e_compensator_original_stopped_signed_L1_physical_clock_autofinite
      X NX (by intro ω; rfl) K (by intro ω; rfl) M rfl T S rfl
      hSm MT N rfl μ hμclock rfl
      (fun ω => (σ ω : ℝ≥0∞)) hσ F hFm hFint H rfl hHsup
  simpa only [H, NX, μT, ENNReal.coe_le_coe] using hRes
