-- Prove2me | solution 1 for CompactnessConjecture.fintype_card_sigma_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/3ae5de39-b9a9-463f-b055-4c2fe96203b9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {α : Type*} [Fintype α]
    {β : α → Type*} [∀ a, Fintype (β a)]
    {baseLower fiberLower : ℕ}
    (hbase : baseLower ≤ Fintype.card α)
    (hfiber : ∀ a : α, fiberLower ≤ Fintype.card (β a)) :
    baseLower * fiberLower ≤ Fintype.card (Sigma β) := by
  classical
  rw [Fintype.card_sigma]
  calc
    baseLower * fiberLower ≤ Fintype.card α * fiberLower :=
      Nat.mul_le_mul_right fiberLower hbase
    _ = ∑ _a : α, fiberLower := by simp
    _ ≤ ∑ a : α, Fintype.card (β a) :=
      Finset.sum_le_sum fun a _ => hfiber a
end CompactnessConjecture
