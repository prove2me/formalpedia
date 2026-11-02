-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:56:39.320938+00:00
-- url     : https://prove2.me/submissions/313a3d1b-e12c-417e-90a4-6d3bb099c7d9

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) ∧
    StronglyAdapted 𝓕
      (fun t ω => X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by
  have hA : StronglyAdapted 𝓕 X.X := by
    intro t
    exact (X.adapted t).stronglyMeasurable
  have hL : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => X.X s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    exact X.leftLim ω t ht
  have hPre : StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s => X.X s ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits X.X hA hL
  refine ⟨hPre, ?_⟩
  intro t
  exact (hA t).sub (hPre t)
