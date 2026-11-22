-- Prove2me | solution 1 for CircuitComplexity.Valiant.exists_r_levels_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:42.683653+00:00
-- url     : https://prove2.me/submissions/c82494d6-7f8d-4fd0-aec7-acd0a04e0a11

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
public import Theorems.Thm_CircuitComplexity_Valiant_sum_card_levelEdges_eq
section
@[expose] public section
namespace Digraph
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
section LegalLabelHelpers
variable {V : Type*}
end LegalLabelHelpers
variable [DecidableEq V]
private lemma exists_r_subset_sum_le
    {α : Type*} (a : α → ℕ) :
    ∀ (n : ℕ) (s : Finset α), s.card = n → ∀ (r : ℕ), r ≤ n →
      ∃ I ⊆ s, I.card = r ∧ n * (∑ i ∈ I, a i) ≤ r * (∑ i ∈ s, a i) := by
  classical
  intro n
  induction n with
  | zero =>
    simp_all
  | succ n' ih =>
    intro s hs r hr
    by_cases hr_eq : r = n' + 1
    · subst hr_eq
      exact ⟨s, Finset.Subset.refl _, hs, le_refl _⟩
    · have hr_lt : r ≤ n' := by omega
      have hs_ne : s.Nonempty := Finset.card_pos.mp (by rw [hs]; omega)
      obtain ⟨jmax, hjmax_mem, hjmax_max⟩ := s.exists_max_image a hs_ne
      let s' := s.erase jmax
      have hs'_card : s'.card = n' := by
        simp [s', Finset.card_erase_of_mem hjmax_mem, hs]
      obtain ⟨I, hI_sub, hI_card, hI_le⟩ := ih s' hs'_card r hr_lt
      refine ⟨I, hI_sub.trans (Finset.erase_subset _ _), hI_card, ?_⟩
      have hsum_s : ∑ i ∈ s, a i = ∑ i ∈ s', a i + a jmax :=
        (Finset.sum_erase_add _ _ hjmax_mem).symm
      have hsumI_le : ∑ i ∈ I, a i ≤ I.card * a jmax := by
        have hbound : ∀ i ∈ I, a i ≤ a jmax := fun i hi =>
          hjmax_max i (hI_sub.trans (Finset.erase_subset _ _) hi)
        exact Finset.sum_le_card_nsmul I a (a jmax) hbound
      rw [hI_card] at hsumI_le
      rw [hsum_s]
      have h_lhs_expand :
          (n' + 1) * (∑ i ∈ I, a i) =
            n' * (∑ i ∈ I, a i) + (∑ i ∈ I, a i) := by ring
      have h_rhs_expand :
          r * (∑ i ∈ s', a i + a jmax) = r * (∑ i ∈ s', a i) + r * a jmax := by ring
      rw [h_lhs_expand, h_rhs_expand]
      have hih_step : n' * (∑ i ∈ I, a i) ≤ r * (∑ i ∈ s', a i) := hI_le
      omega
end CircuitComplexity.Valiant
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace CircuitComplexity.Valiant
theorem _root_.solution
    (G : Digraph V) [DecidableRel G.Adj] {k r : ℕ} (hrk : r ≤ k)
    (hac : IsAcyclic G) (hd : G.depth ≤ 2 ^ k) :
    ∃ I : Finset ℕ, I ⊆ Finset.Ioc 0 k ∧ I.card = r ∧
      k * (∑ i ∈ I, (levelEdges G k i).card) ≤ r * G.edgeFinset.card := by
  have hsum : ∑ i ∈ Finset.Ioc 0 k, (levelEdges G k i).card = G.edgeFinset.card :=
    sum_card_levelEdges_eq G hac hd
  have hcard : (Finset.Ioc 0 k).card = k := by simp
  obtain ⟨I, hI_sub, hI_card, hI_le⟩ :=
    exists_r_subset_sum_le (fun i => (levelEdges G k i).card)
      k (Finset.Ioc 0 k) hcard r hrk
  refine ⟨I, hI_sub, hI_card, ?_⟩
  simp_all
end CircuitComplexity.Valiant
