-- Prove2me | solution 1 for AvramDividend.Classical.record_survival_finite_horizon_stopped_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:06:26.83846+00:00
-- url     : https://prove2.me/submissions/eb54aec3-0098-4147-9640-a153a2edc86e

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_record_survival_stopped_history_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ) (M : ℝ≥0) :
    MeasurableSet[
      ((upperPassage_stopping_rightCont_filtration X b).min_const M).measurableSpace]
      {ω : Ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (M : ℝ≥0∞)} := by
  let hτ := upperPassage_stopping_rightCont_filtration X b
  let A : Set Ω := {ω | twoSidedExitUpTime X b ω < barrierRuinTime X a ω}
  let B : Set Ω := {ω | twoSidedExitUpTime X b ω ≤ (M : ℝ≥0∞)}
  have hA : MeasurableSet[hτ.measurableSpace] A :=
    record_survival_stopped_history_measurable X a b
  have hB : MeasurableSet[hτ.measurableSpace] B := hτ.measurableSet_le' M
  have hAM : MeasurableSet[𝓕.rightCont M] (A ∩ B) :=
    ((hτ.measurableSet A).mp hA).2 M
  have hmin := (hτ.measurableSet_min_const_iff (A ∩ B)).mpr
    ⟨hA.inter hB, hAM⟩
  simpa only [A, B, Set.setOf_and] using hmin
