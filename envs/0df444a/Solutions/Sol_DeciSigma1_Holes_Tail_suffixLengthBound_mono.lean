-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:47.553804+00:00
-- url     : https://prove2.me/submissions/fcb9f863-be1d-459f-8888-b94a5b4df22a

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_factorLengthBound_mono
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


attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthBound m N Ss)
  | [] => fun b b' h => by simp only [suffixLengthBound_nil];
                           exact Nat.add_le_add_right (factorLengthBound_mono m N h) 1
  | S :: Ss => fun b b' h => by
    have hg := solution m N Ss
    have hG : Monotone (fun b => b + suffixLengthBound m N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthBound_cons, suffixLengthBound_cons]
    have h2 := hg h1
    have h3 := hg (Nat.add_le_add h1 h2)
    omega
end DeciSigma1.Holes.Tail
