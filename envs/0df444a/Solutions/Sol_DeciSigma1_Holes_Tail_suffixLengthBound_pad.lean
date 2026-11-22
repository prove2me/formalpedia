-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthBound_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:05.238894+00:00
-- url     : https://prove2.me/submissions/288c23ab-6b95-4efc-9cb7-636aa74b778f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_chainBound_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_ChainBound_chainBoundFrom
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
variable [DecidableEq α] [Fintype S]
variable (T : Readers.Table α S k) (q0 : S) (x : List α)
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (ts : List (List α)) {m S b₀ : ℕ} (hm : ts.length ≤ m)
    (hS : ∀ t ∈ ts, ChainBoundFrom t b₀ S) :
    ∃ ts' : List (List α), (∀ t ∈ ts, t ∈ ts') ∧
        List.Forall₂ (fun t S => ChainBoundFrom t b₀ S) ts' (List.replicate m S) := by
  induction m generalizing ts with
  | zero =>
    obtain rfl : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp, .nil⟩
  | succ m ih =>
    cases ts with
    | nil =>
      obtain ⟨ts', _, h⟩ := ih [] (by simp) (by simp)
      exact ⟨[] :: ts', by simp, .cons ((chainBound_nil S).chainBoundFrom b₀) h⟩
    | cons t ts =>
      obtain ⟨ts', h1, h2⟩ := ih ts (by simp at hm; omega)
        (fun t' ht' => hS t' (List.mem_cons_of_mem _ ht'))
      refine ⟨t :: ts', fun t' ht' => ?_, .cons (hS t List.mem_cons_self) h2⟩
      rcases List.mem_cons.mp ht' with rfl | ht'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h1 t' ht')
end DeciSigma1.Holes.Tail
