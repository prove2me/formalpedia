-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_union_Ico_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:00.530557+00:00
-- url     : https://prove2.me/submissions/20985c89-b2f7-42ac-9337-404c5d50e8f9

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_congr

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
variable {c δ : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {p : ℕ} (hp : p ≤ c) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D p :=
  retainedCount_congr fun i hi => by
    rw [Finset.mem_union, Finset.mem_Ico]
    exact ⟨fun h => h.elim id fun h => by omega, Or.inl⟩
end DeciSigma1.Words
