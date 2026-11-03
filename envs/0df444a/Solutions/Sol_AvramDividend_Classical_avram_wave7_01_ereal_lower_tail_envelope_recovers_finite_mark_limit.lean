-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_ereal_lower_tail_envelope_recovers_finite_mark_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:54:10.936733+00:00
-- url     : https://prove2.me/submissions/86991165-96dc-46d6-9ac0-18829121fe7e

import Mathlib
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A finite EReal sequence limit is its converted tail lower envelope. -/
theorem solution
    (a : ℕ → EReal) (l : ℝ)
    (h : Tendsto a atTop (𝓝 (l : EReal))) :
    EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
      if m ≤ n then a n else ⊤) = l := by
  classical
  have hTail :
      (⨆ m : ℕ, ⨅ n : ℕ, if m ≤ n then a n else ⊤) =
        Filter.liminf a Filter.atTop := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    apply iSup_congr
    intro m
    apply iInf_congr
    intro n
    by_cases hmn : m ≤ n
    · simp [hmn]
    · simp [hmn]
  calc
    EReal.toReal (⨆ m : ℕ, ⨅ n : ℕ,
        if m ≤ n then a n else ⊤) =
        EReal.toReal (Filter.liminf a Filter.atTop) := by rw [hTail]
    _ = l := by
      rw [h.liminf_eq]
      exact EReal.toReal_coe l
