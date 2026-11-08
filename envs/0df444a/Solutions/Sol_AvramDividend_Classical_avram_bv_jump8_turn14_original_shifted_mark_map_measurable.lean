-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn14_original_shifted_mark_map_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:30:23.476732+00:00
-- url     : https://prove2.me/submissions/5cdf911e-c15b-4c62-9500-cbff70f2875a

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

/-- The actual marked-jump map of a shifted Lévy increment path is Borel
for every deterministic shift, including nonintegral equal-cell boundaries. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0) :
    Measurable (fun u : ℝ≥0 =>
      (u, (X.X (s + u) ω - X.X s ω) -
        Function.leftLim
          (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)) := by
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  have hXPath : Measurable (fun u : ℝ≥0 => X.X u ω) :=
    hXJoint.comp (measurable_id.prodMk measurable_const)
  have hShiftPath : Measurable (fun u : ℝ≥0 =>
      X.X (s + u) ω - X.X s ω) :=
    (hXPath.comp (measurable_const.add measurable_id)).sub measurable_const
  have hCad := avram_wave7_01_original_shifted_future_increment_path_cadlag
    X ω s
  let F : ℝ≥0 → Unit → ℝ := fun t _ =>
    X.X (s + t) ω - X.X s ω
  have hFJoint : Measurable (fun z : ℝ≥0 × Unit => F z.1 z.2) :=
    hShiftPath.comp measurable_fst
  have hFLeftJoint :
      Measurable (fun z : ℝ≥0 × Unit =>
        Function.leftLim (fun r : ℝ≥0 => F r z.2) z.1) :=
    avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
      F hFJoint
      (by
        change Measurable (fun _ : Unit =>
          Function.leftLim (fun r : ℝ≥0 =>
            X.X (s + r) ω - X.X s ω) 0)
        exact measurable_const)
      (by intro _ t ht; exact hCad.2 t ht)
  have hLeft : Measurable (fun u : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 =>
        X.X (s + v) ω - X.X s ω) u) := by
    change Measurable (fun u : ℝ≥0 =>
      Function.leftLim (fun v : ℝ≥0 => F v (():Unit)) u)
    have hEmbed : Measurable (fun u : ℝ≥0 => (u, (():Unit))) :=
      Measurable.prodMk measurable_id measurable_const
    exact hFLeftJoint.comp hEmbed
  exact Measurable.prodMk measurable_id (hShiftPath.sub hLeft)
