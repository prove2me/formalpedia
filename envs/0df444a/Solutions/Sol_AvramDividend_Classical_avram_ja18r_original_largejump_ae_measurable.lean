-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18r_original_largejump_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:07:39.584703+00:00
-- url     : https://prove2.me/submissions/c6fc9735-686c-4221-aaec-1eecf0c73450

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys55_original_intrinsic_NX_measure_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys57_ae_finite_supported_random_integral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      AEStronglyMeasurable
        (fun ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) P := by
  intro t
  let M : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let S : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)
  have hMS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Iic
  have hSubset : S ⊆ Ioc (0 : ℝ≥0) t ×ˢ
      {y : ℝ | (1 : ℝ) ≤ dist y 0} := by
    intro p hp
    rcases hp with ⟨ht, hz⟩
    refine ⟨ht, ?_⟩
    have hz0 : p.2 ≤ (0 : ℝ) := le_trans hz (by norm_num)
    have hzle : p.2 ≤ (-1 : ℝ) := hz
    have hbound : (1 : ℝ) ≤ -p.2 := by linarith
    simpa [Real.dist_eq, abs_of_nonpos hz0] using hbound
  have hFiniteMeasure : ∀ᵐ ω ∂P, M ω S < ⊤ := by
    filter_upwards [] with ω
    exact lt_of_le_of_lt (measure_mono hSubset)
      (avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
        X ω t 1 (by norm_num))
  have hM : Measurable M :=
    avram_bvb_phys55_original_intrinsic_NX_measure_measurable X
  have hM_eval : ∀ B : Set (ℝ≥0 × ℝ), MeasurableSet B →
      Measurable (fun ω => M ω B) :=
    Measure.measurable_measure.mp hM
  let f : Ω × (ℝ≥0 × ℝ) → ℝ := fun q =>
    if q.2 ∈ S then q.2.2 else 0
  have hf : StronglyMeasurable f := by
    apply Measurable.stronglyMeasurable
    exact Measurable.ite (hMS.preimage measurable_snd)
      (measurable_snd.snd) measurable_const
  have hfS : ∀ ω p, p ∉ S → f (ω, p) = 0 := by
    intro ω p hp
    simp [f, hp]
  have h := avram_bvb_phys57_ae_finite_supported_random_integral_measurable
    P M hM_eval S hMS f hf hfS hFiniteMeasure
  have hEq : (fun ω : Ω => ∫ p, f (ω, p) ∂M ω) =
      (fun ω : Ω => avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) := by
    funext ω
    change (∫ p, (if p ∈ S then p.2 else 0) ∂M ω) =
      (∫ p in S, p.2 ∂M ω)
    have hindicator : (fun p : ℝ≥0 × ℝ =>
        if p ∈ S then p.2 else 0) =
        S.indicator (fun p => p.2) := by
      funext p
      simp [Set.indicator]
    rw [hindicator]
    exact integral_indicator hMS
  simpa only [hEq] using h
