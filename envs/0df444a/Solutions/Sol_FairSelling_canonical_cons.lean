-- Prove2me | solution 1 for FairSelling.canonical_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:36.206839+00:00
-- url     : https://prove2.me/submissions/aec265b1-a721-4111-8329-3ccc2d723cbb

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution {w p : G → ℝ} {μ t : ℝ} {k : ℕ} {R R' new : Finset G} {D : ℝ}
    (hD : 0 ≤ D) (hR' : R' ⊆ R) (hnew : new ⊆ R) (hdisj : Disjoint new R')
    (hacc : t ≤ vbarSum w p new)
    (h : CanonExists w p μ t k R' D) :
    CanonExists w p μ t (k + 1) R D := by
  classical
  intro _
  haveI : NeZero (k + 1) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- no other part: the new part is the special part
    subst hk
    exact ⟨{ goods := fun _ => new
             sell := ∅
             src := fun _ => none
             dcash := fun _ => 0
             scash := fun _ => 0
             goods_subset := fun _ => hnew
             goods_disj := fun j j' hjj =>
               absurd (Fin.ext (by have := j.isLt; have := j'.isLt; omega)) hjj
             sell_subset := by simp
             sell_disj := fun _ => by simp
             src_mem := fun j f hf => by simp at hf
             dcash_nonneg := fun _ => le_rfl
             scash_nonneg := fun _ => le_rfl
             dcash_sum := by simpa using hD
             scash_sum := fun f hf => by simp at hf
             scash_zero := fun _ _ => rfl
             price_large := fun f hf => by simp at hf
             acceptable := fun _ => by simpa using hacc
             pure_or_singleton := fun _ _ => Or.inl rfl
             singleton_dcash := fun _ _ h => absurd rfl h
             singleton_cond := fun _ _ h => absurd rfl h }⟩
  · haveI : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
    obtain ⟨C⟩ := h hk
    have hlast : ¬ ((Fin.last k : Fin (k + 1)) : ℕ) < k := by simp
    have hgoods_disj_new : ∀ j : Fin k, Disjoint new (C.goods j) :=
      fun j => Finset.disjoint_of_subset_right (C.goods_subset j) hdisj
    refine ⟨{ goods := fun j => if h : (j : ℕ) < k then C.goods ⟨j, h⟩ else new
              sell := C.sell
              src := fun j => if h : (j : ℕ) < k then C.src ⟨j, h⟩ else none
              dcash := fun j => if h : (j : ℕ) < k then C.dcash ⟨j, h⟩ else 0
              scash := fun j => if h : (j : ℕ) < k then C.scash ⟨j, h⟩ else 0
              goods_subset := ?_
              goods_disj := ?_
              sell_subset := C.sell_subset.trans hR'
              sell_disj := ?_
              src_mem := ?_
              dcash_nonneg := ?_
              scash_nonneg := ?_
              dcash_sum := ?_
              scash_sum := ?_
              scash_zero := ?_
              price_large := C.price_large
              acceptable := ?_
              pure_or_singleton := ?_
              singleton_dcash := ?_
              singleton_cond := ?_ }⟩
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact (C.goods_subset _).trans hR'
      · simp only [dif_neg hj]; exact hnew
    · intro j j' hjj
      by_cases hj : (j : ℕ) < k <;> by_cases hj' : (j' : ℕ) < k
      · simp only [dif_pos hj, dif_pos hj']
        exact C.goods_disj _ _ (fun h => hjj (Fin.ext (by simpa using congrArg Fin.val h)))
      · simp only [dif_pos hj, dif_neg hj']
        exact (hgoods_disj_new _).symm
      · simp only [dif_neg hj, dif_pos hj']
        exact hgoods_disj_new _
      · exact absurd (Fin.ext (by omega : (j : ℕ) = (j' : ℕ))) hjj
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.sell_disj _
      · simp only [dif_neg hj]
        exact Finset.disjoint_of_subset_left C.sell_subset hdisj.symm
    · intro j f hf
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hf; exact C.src_mem _ f hf
      · rw [dif_neg hj] at hf; exact absurd hf (by simp)
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.dcash_nonneg _
      · simp only [dif_neg hj]; exact le_rfl
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.scash_nonneg _
      · simp only [dif_neg hj]; exact le_rfl
    · have hcast : ∀ j : Fin k,
          (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.dcash ⟨(j.castSucc : ℕ), h⟩ else 0)
            = C.dcash j := by
        intro j
        rw [dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp)]
        exact congrArg C.dcash (Fin.ext (by simp))
      rw [Fin.sum_univ_castSucc, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hcast j),
        dif_neg hlast, add_zero]
      exact C.dcash_sum
    · intro f hf
      have hstep : ∑ j ∈ Finset.univ.filter
            (fun j : Fin (k + 1) => (if h : (j : ℕ) < k then C.src ⟨j, h⟩ else none) = some f),
              (if h : (j : ℕ) < k then C.scash ⟨j, h⟩ else 0)
          = ∑ j ∈ Finset.univ.filter (fun j : Fin k => C.src j = some f), C.scash j := by
        have hcast : ∀ j : Fin k,
            (if (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.src ⟨(j.castSucc : ℕ), h⟩
                  else none) = some f then
              (if h : ((j.castSucc : Fin (k + 1)) : ℕ) < k then C.scash ⟨(j.castSucc : ℕ), h⟩
                else 0) else 0)
              = (if C.src j = some f then C.scash j else 0) := by
          intro j
          rw [dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp),
            dif_pos (show ((j.castSucc : Fin (k + 1)) : ℕ) < k by simp)]
          have hj : (⟨(j.castSucc : ℕ), (by simp : ((j.castSucc : Fin (k+1)) : ℕ) < k)⟩ : Fin k) = j :=
            Fin.ext (by simp)
          rw [hj]
        rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc,
          Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hcast j), dif_neg hlast]
        simp
      rw [hstep]
      exact C.scash_sum f hf
    · intro j hj
      by_cases hjk : (j : ℕ) < k
      · rw [dif_pos hjk] at hj ⊢; exact C.scash_zero _ hj
      · rw [dif_neg hjk]
    · intro j
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]; exact C.acceptable _
      · simp only [dif_neg hj, add_zero]; exact hacc
    · intro j _
      by_cases hj : (j : ℕ) < k
      · simp only [dif_pos hj]
        by_cases hz : (⟨j, hj⟩ : Fin k) = 0
        · -- the special part of `C` sits at index `0`, which is excluded
          exfalso
          have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
          exact absurd (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
            (by assumption)
        · exact C.pure_or_singleton _ hz
      · rw [dif_neg hj]; exact Or.inl rfl
    · intro j hjne hsrc
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hsrc ⊢
        refine C.singleton_dcash _ (fun hz => ?_) hsrc
        have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
        exact hjne (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
      · rw [dif_neg hj] at hsrc; exact absurd rfl hsrc
    · intro j hjne hsrc e he f hf
      by_cases hj : (j : ℕ) < k
      · rw [dif_pos hj] at hsrc he
        refine C.singleton_cond _ (fun hz => ?_) hsrc e he f hf
        have hj0 : (j : ℕ) = 0 := by simpa using congrArg Fin.val hz
        exact hjne (Fin.ext (show (j : ℕ) = ((0 : Fin (k + 1)) : ℕ) by simp [hj0]))
      · rw [dif_neg hj] at hsrc; exact absurd rfl hsrc
end FairSelling
