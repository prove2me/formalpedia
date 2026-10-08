-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_offset_of_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T17:39:02.441858+00:00
-- url     : https://prove2.me/submissions/44f66629-b264-4a15-bb8a-a964815c6ab7

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (t : ℝ≥0) (ω : Ω) :
    barrierStrategy X x a t ω =
      max 0 (barrierStrategy X a a t ω - (a - x)) := by
  classical
  unfold barrierStrategy
  by_cases ht : t = 0
  · simp only [if_pos ht]
    have hb : 0 ≤ a - x := sub_nonneg.mpr hxa
    have hz : (0 : ℝ) - (a - x) ≤ 0 := by linarith
    exact (max_eq_left hz).symm
  · simp only [if_neg ht, sub_self, zero_add]
    let S : ℝ := ⨆ s : Icc (0 : ℝ≥0) t, X.X s ω
    change max 0 (x - a + S) = max 0 (max 0 S - (a - x))
    have hrearrange : x - a + S = S - (a - x) := by ring
    rw [hrearrange]
    have hb : 0 ≤ a - x := sub_nonneg.mpr hxa
    by_cases hs : 0 ≤ S
    · rw [max_eq_right hs]
    · have hs0 : S ≤ 0 := le_of_not_ge hs
      have hleft : S - (a - x) ≤ 0 := by linarith
      have hright : (0 : ℝ) - (a - x) ≤ 0 := by linarith
      rw [max_eq_left hs0, max_eq_left hleft, max_eq_left hright]
