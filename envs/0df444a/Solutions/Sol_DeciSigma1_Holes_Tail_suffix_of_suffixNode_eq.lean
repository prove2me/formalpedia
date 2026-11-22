-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffix_of_suffixNode_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:35.873138+00:00
-- url     : https://prove2.me/submissions/52a8d1ca-de2a-4bbc-973d-145c82a101ca

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixNode_suffix
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (T : Table α S k) (q0 : S) {w w' p : List α}
    (he : suffixNode T q0 D w = suffixNode T q0 D w') (hp : p <:+ w) (hpD : p ∈ D) :
    p <:+ w' ∧ runFrom T.step q0 (w'.take (w'.length - p.length)) =
      runFrom T.step q0 (w.take (w.length - p.length)) := by
  obtain ⟨h1, h2⟩ := suffixNode_suffix T q0 hp hpD
  rw [he] at h1 h2
  have hp' : p <:+ w' := h1.trans (dictSuffix_suffix D w')
  exact ⟨hp', (suffixNode_suffix T q0 hp' hpD).2.trans h2.symm⟩
end DeciSigma1.Holes.Tail
