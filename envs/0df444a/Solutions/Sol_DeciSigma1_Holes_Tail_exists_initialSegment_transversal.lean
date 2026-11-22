-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_initialSegment_transversal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:13.363562+00:00
-- url     : https://prove2.me/submissions/fcff4e55-1c2d-46ed-bf27-2876342e588c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
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



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution {β : Type*} [DecidableEq β] {n K : ℕ} (f : Fin n → β)
    (hK : K ≤ (Finset.univ.image f).card) :
    ∃ (m : ℕ) (R : Finset (Fin n)), (∀ i ∈ R, i.val < m) ∧ Set.InjOn f R ∧ R.card = K ∧
      ((Finset.univ.filter fun i : Fin n => i.val < m).image f).card = K := by
  classical
  set pre : ℕ → Finset (Fin n) := fun m => Finset.univ.filter fun i => i.val < m
  -- the number of values on `pre m` grows by at most one with `m`
  have hstep : ∀ m, ((pre (m + 1)).image f).card ≤ ((pre m).image f).card + 1 := by
    intro m
    have : pre (m + 1) = pre m ∪ Finset.univ.filter fun i => i.val = m := by
      ext i; simp only [pre, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [this, Finset.image_union]
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le.trans ?_) _)
    exact Finset.card_le_one.mpr fun i hi j hj => Fin.ext (by simp at hi hj; omega)
  have hvalue : ∀ m, K ≤ ((pre m).image f).card → ∃ m', ((pre m').image f).card = K := by
    intro m
    induction m with
    | zero => intro h; exact ⟨0, by simp [pre] at h ⊢; omega⟩
    | succ m ih =>
      intro h
      by_cases h' : K ≤ ((pre m).image f).card
      · exact ih h'
      · exact ⟨m + 1, by have := hstep m; omega⟩
  obtain ⟨m, hm⟩ := hvalue n (by simp only [pre]; rwa [Finset.filter_true_of_mem fun i _ => i.isLt])
  obtain ⟨R, hRm, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (↑(pre m))
    ((pre m).image f) (by rw [Finset.coe_image]; exact Set.surjOn_image _ _)
  refine ⟨m, R, fun i hi => (Finset.mem_filter.mp (hRm hi)).2, hinj, ?_, hm⟩
  rw [← Finset.card_image_of_injOn hinj, himg, hm]
end DeciSigma1.Holes.Tail
