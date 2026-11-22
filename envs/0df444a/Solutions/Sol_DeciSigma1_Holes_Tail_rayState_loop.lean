-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.rayState_loop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:01.285821+00:00
-- url     : https://prove2.me/submissions/ea61dd57-7169-468e-aaa2-af37dda892e0

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
public import Theorems.Thm_DeciSigma1_Holes_Tail_rayState_add
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
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (q : S) (Ω : Ray α) {x d : ℕ}
    (hxd : rayState M q Ω (x + d) = rayState M q Ω x)
    (hshift : ∀ s, Ω.stream (x + d + s) = Ω.stream (x + s)) :
    ∀ m t, rayState M q Ω (x + t + m * d) = rayState M q Ω (x + t) := by
  have hf : (fun i => Ω.stream (x + d + i)) = fun i => Ω.stream (x + i) := funext hshift
  have hloop : ∀ t, rayState M q Ω (x + d + t) = rayState M q Ω (x + t) := by
    intro t
    rw [rayState_add q Ω (x + d) t, hxd, hf, ← rayState_add]
  intro m
  induction m with
  | zero => intro t; simp
  | succ m ih =>
    intro t
    rw [show x + t + (m + 1) * d = x + d + (t + m * d) by ring, hloop, ← Nat.add_assoc, ih]
end DeciSigma1.Holes.Tail
