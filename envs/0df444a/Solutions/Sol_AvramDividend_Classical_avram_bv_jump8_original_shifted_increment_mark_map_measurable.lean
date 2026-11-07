-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_original_shifted_increment_mark_map_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:34:46.368419+00:00
-- url     : https://prove2.me/submissions/dc083bca-b9a9-445d-a8c8-1a3dd991f111

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    Measurable (fun u : ℝ≥0 =>
      (u, (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
        Function.leftLim
          (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω -
            X.X (n : ℝ≥0) ω) u)) := by
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  have hXPath : Measurable (fun u : ℝ≥0 => X.X u ω) :=
    hXJoint.comp (measurable_id.prodMk measurable_const)
  have hShiftPath : Measurable (fun u : ℝ≥0 =>
      X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) :=
    (hXPath.comp (measurable_const.add measurable_id)).sub measurable_const
  have hCad := avram_wave7_01_original_shifted_future_increment_path_cadlag
    X ω (n : ℝ≥0)
  let F : ℝ≥0 → Unit → ℝ := fun t _ =>
    X.X ((n : ℝ≥0) + t) ω - X.X (n : ℝ≥0) ω
  have hFJoint : Measurable (fun z : ℝ≥0 × Unit => F z.1 z.2) :=
    hShiftPath.comp measurable_fst
  have hFLeftJoint :
      Measurable (fun z : ℝ≥0 × Unit =>
        Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1) :=
    avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
      F hFJoint
      (by
        change Measurable (fun _ : Unit =>
          Function.leftLim (fun s : ℝ≥0 =>
            X.X ((n : ℝ≥0) + s) ω - X.X (n : ℝ≥0) ω) 0)
        exact measurable_const)
      (by intro _ t ht; exact hCad.2 t ht)
  have hLeft : Measurable (fun u : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 =>
        X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u) := by
    change Measurable (fun u : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 => F v (():Unit)) u)
    have hEmbed : Measurable (fun u : ℝ≥0 => (u, (():Unit))) :=
      Measurable.prodMk measurable_id measurable_const
    exact hFLeftJoint.comp hEmbed
  exact Measurable.prodMk measurable_id (hShiftPath.sub hLeft)
