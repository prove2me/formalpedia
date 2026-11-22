-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.ClosedAt.nodeClosedAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:32.430588+00:00
-- url     : https://prove2.me/submissions/f91cf70b-4d5e-48ef-85f2-8c48c661d7e6

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixNode_append
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
namespace ClosedAt
theorem _root_.solution (hcl : ClosedAt T q0 x B c c') (hD : [] ∈ D)
    (hB : ∀ r ∈ D, r.length ≤ B) : NodeClosedAt T q0 D x c c' := by
  obtain ⟨hBc, hcc, hc', hw⟩ := hcl
  refine ⟨hcc, hc', ?_⟩
  have hsplit : ∀ e, x.take e = x.take (e - B) ++ (x.take e).drop (e - B) := fun e => by
    conv_lhs => rw [← List.take_append_drop (e - B) (x.take e)]
    rw [List.take_take, min_eq_left (Nat.sub_le _ _)]
  have hlen : ∀ e, B ≤ e → e ≤ x.length → ((x.take e).drop (e - B)).length = B := fun e h1 h2 => by
    simp; omega
  rw [hsplit c, hsplit c', suffixNode_append T q0 hD (by rw [hlen c hBc (by omega)]; exact hB),
    suffixNode_append T q0 hD (by rw [hlen c' (by omega) hc']; exact hB)]
  simp only [windowState, Prod.mk.injEq] at hw
  rw [hw.1, hw.2]
end ClosedAt
end DeciSigma1.Holes.Tail
