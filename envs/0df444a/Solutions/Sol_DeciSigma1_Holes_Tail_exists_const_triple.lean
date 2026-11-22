-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_const_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:34.898842+00:00
-- url     : https://prove2.me/submissions/314cc8cd-bb1c-4c93-aa3f-49888103631c

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Levels
public import Theorems.Thm_DeciSigma1_Holes_Tail_exists_forall_of_card_filter_not_le
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
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



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hmono : ∀ x l, P x l → P x (l + 1)) :
    ∃ j, j ≤ Fintype.card ι ∧ ∀ x, (P x (3 * j) ↔ P x (3 * j + 2)) := by
  classical
  have hmono' : ∀ x l l', l ≤ l' → P x l → P x l' := by
    intro x l l' hl
    induction l', hl using Nat.le_induction with
    | base => exact id
    | succ l' _ ih => exact fun h => hmono x _ (ih h)
  have key : ∀ x j, ¬ (P x (3 * j) ↔ P x (3 * j + 2)) → ¬ P x (3 * j) ∧ P x (3 * j + 2) := by
    intro x j hj
    by_cases h0 : P x (3 * j)
    · exact absurd ⟨fun _ => hmono' x _ _ (by omega) h0, fun _ => h0⟩ hj
    · refine ⟨h0, ?_⟩
      by_contra h2
      exact hj ⟨fun h => absurd h h0, fun h => absurd h h2⟩
  -- each predicate changes in at most one triple
  obtain ⟨j, hj, hjP⟩ := exists_forall_of_card_filter_not_le
    (R := Finset.range (Fintype.card ι + 1)) (U := Finset.univ)
    (fun x j => P x (3 * j) ↔ P x (3 * j + 2)) (c := 1) (fun x _ => by
      rw [Finset.card_le_one]
      intro j hj j' hj'
      simp only [Finset.mem_filter] at hj hj'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (key x j' hj'.2).1 (hmono' x _ _ (by omega) (key x j hj.2).2)
      · exact (key x j hj.2).1 (hmono' x _ _ (by omega) (key x j' hj'.2).2)) (by simp)
  exact ⟨j, by simp at hj; omega, fun x => hjP x (Finset.mem_univ x)⟩
end DeciSigma1.Holes.Tail
