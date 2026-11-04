-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_past_event_countable_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:46:08.599457+00:00
-- url     : https://prove2.me/submissions/92dfc326-b4e2-465d-92aa-42f08c61e175

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Campbell expectations of original intrinsic jump counts are countably
additive on arbitrary disjoint Borel time-mark regions over every past event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (C : ℕ → Set (ℝ≥0 × ℝ))
    (hC : ∀ n, MeasurableSet (C n))
    (hDisj : Pairwise (Function.onFun Disjoint C)) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, C n) ∂P) =
    ∑' n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (C n) ∂P) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure X s A hA
  have hUnion : MeasurableSet (⋃ n, C n) := MeasurableSet.iUnion hC
  calc
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, C n) ∂P) = Q (⋃ n, C n) := (hQ _ hUnion).symm
    _ = ∑' n, Q (C n) := measure_iUnion hDisj hC
    _ = ∑' n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (C n) ∂P) := by
      congr 1
      funext n
      exact hQ (C n) (hC n)
