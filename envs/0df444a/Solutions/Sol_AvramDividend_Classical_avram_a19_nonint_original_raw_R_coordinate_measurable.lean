-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_nonint_original_raw_R_coordinate_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:06:04.132871+00:00
-- url     : https://prove2.me/submissions/1e0a2b50-a252-4183-9f7b-39b49f4e590e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ t : ℝ≥0, AEStronglyMeasurable (fun ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)) P := by
  intro t
  have hXt : Measurable (fun ω : Ω => X.X t ω) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (measurable_const.prodMk measurable_id)
  have hJ :=
    avram_route11_original_raw_jump_cumulative_aestronglyMeasurable
      X hX hBV t
  exact (measurable_const.sub hXt).aestronglyMeasurable.sub hJ
