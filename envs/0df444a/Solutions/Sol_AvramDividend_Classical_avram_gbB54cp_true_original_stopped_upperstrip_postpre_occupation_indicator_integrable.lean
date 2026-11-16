-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_true_original_stopped_upperstrip_postpre_occupation_indicator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:31:55.959535+00:00
-- url     : https://prove2.me/submissions/09f6c671-8481-49ff-9eff-01ed4caa520a

import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_postpayment_real_time_reserve_measurable_path
import Theorems.Thm_AvramDividend_Classical_avram_gfinite67_original_real_time_cap_strip_joint_measurable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x b : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (ω : Ω) :
    IntegrableOn
      (fun t : ℝ => if t < (ρ ω : ℝ) ∧
        b < x + X.X (Real.toNNReal t) ω -
          rightLimit D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume ∧
    IntegrableOn
      (fun t : ℝ => if t < (ρ ω : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0)
      (Ioo (0 : ℝ) (n : ℝ)) volume := by
  classical
  let S : Set ℝ := Ioo (0 : ℝ) (n : ℝ)
  let μ : Measure ℝ := volume.restrict S
  have hOne : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) S volume
    refine integrableOn_const ?_ ?_
    · change volume (Ioo (0 : ℝ) (n : ℝ)) ≠ ⊤
      exact ne_of_lt measure_Ioo_lt_top
    · norm_num
  have hY : Measurable (fun t : ℝ =>
      x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω) :=
    avram_gbB42_original_postpayment_real_time_reserve_measurable_path
      X x D hD ω
  have hTime : MeasurableSet {t : ℝ | t < (ρ ω : ℝ)} :=
    measurableSet_lt measurable_id measurable_const
  have hPost : MeasurableSet {t : ℝ |
      t < (ρ ω : ℝ) ∧
      b < x + X.X (Real.toNNReal t) ω -
        rightLimit D (Real.toNNReal t) ω} :=
    hTime.inter (measurableSet_lt measurable_const hY)
  have hJoint :=
    avram_gfinite67_original_real_time_cap_strip_joint_measurable
      X x D hD ρ hρstop b
  have hPre : MeasurableSet {t : ℝ |
      t < (ρ ω : ℝ) ∧
      b < riskProcess X x D (Real.toNNReal t) ω} := by
    have hmap : Measurable (fun t : ℝ => (t, ω)) :=
      measurable_id.prodMk measurable_const
    simpa only [Set.preimage_setOf_eq] using hJoint.preimage hmap
  have hI (f : ℝ → Prop) [DecidablePred f]
      (hf : MeasurableSet {t : ℝ | f t}) :
      Integrable (fun t => if f t then (1 : ℝ) else 0) μ := by
    apply hOne.mono
    · exact (Measurable.ite hf measurable_const measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by split_ifs <;> norm_num)
  exact ⟨hI _ hPost, hI _ hPre⟩
