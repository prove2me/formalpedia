-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.levelState_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:37.0808+00:00
-- url     : https://prove2.me/submissions/bbdbed62-cca1-49c4-ae47-2d31526c5517

module
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_ElementaryBounds
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_LevelElementaryBound
public import Theorems.Thm_DeciSigma1_Holes_Tail_levelStep_envelope
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_exp2_add
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Holes.Tail
open Arithmetic
private theorem exp2_pos (t : ℕ) : 0 < exp2 t := by
  exact Nat.two_pow_pos t
end DeciSigma1.Holes.Tail
end
end

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open Arithmetic
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (k N A l : ℕ)
    (hA : k + N + levelMultiplicity k N + N * N + 20 ≤ A) :
    stateEnvelope
      (exp2 (((k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5) * l) * A)
      (levelState k N l) := by
  let V := (k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5
  induction l with
  | zero =>
    simp only [Nat.mul_zero, exp2, pow_zero, one_mul, levelState,
      Function.iterate_zero_apply, initialLevelState, stateEnvelope]
    exact ⟨Nat.one_le_pow _ _ (by decide), Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, Nat.zero_le _⟩
  | succ l ih =>
    have hlow : A ≤ exp2 (V * l) * A :=
      Nat.le_mul_of_pos_left A (exp2_pos _)
    have h := levelStep_envelope k N (levelMultiplicity k N) _ (hA.trans hlow) ih
    rw [levelState_succ]
    convert h using 1
    change exp2 (V * (l + 1)) * A = exp2 V * (exp2 (V * l) * A)
    rw [Nat.mul_add, Nat.mul_one, exp2_add]
    ring
end DeciSigma1.Holes.Tail
