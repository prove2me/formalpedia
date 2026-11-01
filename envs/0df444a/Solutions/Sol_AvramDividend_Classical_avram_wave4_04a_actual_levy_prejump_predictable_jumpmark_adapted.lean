-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_predictable_jumpmark_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:36:36.606029+00:00
-- url     : https://prove2.me/submissions/7d0f1bef-51ed-4f91-afbd-75e410c42ab9

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- For the original L\u00e9vy source, pre-jump values are strongly predictable and actual
jump marks are strongly adapted under the same-path right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) ∧
    StronglyAdapted 𝓕.rightCont
      (fun t ω => X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by
  have hA : StronglyAdapted 𝓕.rightCont X.X := by
    intro t
    exact ((X.adapted t).mono (𝓕.le_rightCont t) le_rfl).stronglyMeasurable
  have hL : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => X.X s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    exact X.leftLim ω t ht
  have hStrong : StronglyAdapted 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s => X.X s ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits X.X hA hL
  have hCont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun u => Function.leftLim (fun s => X.X s ω) u) (Iic t) t := by
    intro ω t
    exact avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
      (fun s => X.X s ω) (hL ω) t
  have hPred : IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s => X.X s ω) t) :=
    avram_wave3_04_strongAdapted_leftContinuous_predictable hStrong hCont
  refine ⟨hPred, ?_⟩
  intro t
  exact (hA t).sub (hPred.stronglyAdapted t)
