-- Prove2me | solution 1 for AvramDividend.Classical.nnreal_sInf_union_cap_eq_of_early_member
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:34:04.805415+00:00
-- url     : https://prove2.me/submissions/85b366a3-18ca-451a-907f-55445e9c4322

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Basic

open AvramDividend.Classical Set
open scoped NNReal
theorem solution
    (A : Set ℝ≥0) (H : ℝ≥0)
    (hMember : ∃ a : ℝ≥0, a ∈ A ∧ a ≤ H) :
    sInf (A ∪ {H}) = sInf A := by
  obtain ⟨a, ha, haH⟩ := hMember
  have hne : A.Nonempty := ⟨a, ha⟩
  rw [csInf_union (OrderBot.bddBelow _) hne (OrderBot.bddBelow _) (singleton_nonempty H),
    csInf_singleton]
  exact inf_eq_left.2 ((csInf_le (OrderBot.bddBelow _) ha).trans haH)
