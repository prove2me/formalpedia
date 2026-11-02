-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_prejump_predictable_raw_original_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:05:18.103549+00:00
-- url     : https://prove2.me/submissions/008eb354-874f-4c2c-9d52-f04a60922303

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsStronglyPredictable 𝓕
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) := by
  have hPre : StronglyAdapted 𝓕
      (fun t ω => Function.leftLim (fun s => X.X s ω) t) :=
    (avram_wave5_01_actual_original_raw_filtration_prejump_jumpmark_strongly_adapted X).1
  have hL : ∀ ω (t : ℝ≥0), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => X.X s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    exact X.leftLim ω t ht
  have hCont : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun u => Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)
        (Iic t) t := by
    intro ω t
    exact avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
      (fun s => X.X s ω) (hL ω) t
  exact avram_wave3_04_strongAdapted_leftContinuous_predictable hPre hCont
