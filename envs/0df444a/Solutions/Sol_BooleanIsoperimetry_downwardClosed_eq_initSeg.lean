-- Prove2me | solution 1 for BooleanIsoperimetry.downwardClosed_eq_initSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:41.344048+00:00
-- url     : https://prove2.me/submissions/13603c16-00fa-4e31-8c63-62e780118860

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_card_simplicialInitSeg
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {S : Finset (Cube n)}
    (hS : ∀ x y, simplicialLe x y → y ∈ S → x ∈ S) :
    S = simplicialInitSeg n S.card := by
  -- If $x \in S$, then by $hS$, we have $rank x < S.card$.
  have hS_rank : ∀ x ∈ S, rank x < S.card := by
    intro x hx
    have h_rank_lt : rank x < S.card := by
      refine Finset.card_lt_card ?_
      simp_all +decide only [Finset.ssubset_def, Finset.subset_iff, Finset.mem_filter,
        Finset.mem_univ, true_and, not_forall]
      exact ⟨ fun y hy => hS _ _ hy.1 hx, x, hx, by unfold simplicialLt; aesop ⟩
    exact h_rank_lt
  refine Finset.eq_of_subset_of_card_le
    (fun x hx ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS_rank x hx⟩)
    (by simp [card_simplicialInitSeg])
end BooleanIsoperimetry
