-- Prove2me | solution 2 for FiniteMagmaE677.left_orbit_positive_period
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:37:09.882301+00:00
-- url     : https://prove2.me/submissions/7727df69-141b-447e-aadc-b225d7370468

import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Dynamics.PeriodicPts.Lemmas

universe u

theorem solution
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) :
    ∃ d : ℕ, 0 < d ∧ (op x)^[d] x = x := by
  have hsurj : Function.Surjective (op x) :=
    fun p => ⟨op p (op (op x p) x), (h p x).symm⟩
  have hinj : Function.Injective (op x) :=
    (Finite.surjective_iff_bijective.mp hsurj).1
  have hmem : x ∈ Function.periodicPts (op x) := hinj.mem_periodicPts x
  have hper : Function.IsPeriodicPt (op x) (Fintype.card α).factorial x :=
    Function.isPeriodicPt_factorial_card_of_mem_periodicPts hmem
  exact ⟨(Fintype.card α).factorial, Nat.factorial_pos _, hper⟩
