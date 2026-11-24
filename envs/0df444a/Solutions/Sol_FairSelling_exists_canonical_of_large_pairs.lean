-- Prove2me | solution 1 for FairSelling.exists_canonical_of_large_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:16:37.254218+00:00
-- url     : https://prove2.me/submissions/ca6201ab-23f5-4a30-8663-6cbcf98231ec

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
import Theorems.Thm_FairSelling_fill_exists_pairs

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {μ : ℝ} (hμ : 0 ≤ μ)
    {k : ℕ} [NeZero k] {R : Finset G} {D : ℝ} (hD : 0 ≤ D) {A C S : Finset G}
    (hRdef : R = A ∪ C ∪ S)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hA1 : ∀ g ∈ A, μ / 3 ≤ vbar w p g) (hsmall : ∀ g ∈ R, vbar w p g ≤ 2 * μ / 3)
    (hC1 : ∀ g ∈ C, vbar w p g ≤ μ / 3)
    (hS1 : ∀ g ∈ S, μ / 3 ≤ p g) (hS2 : ∀ g ∈ S, w g ≤ p g)
    {t : ℕ} (hcard : A.card ≤ k + t)
    (hbud : ((k : ℝ) - 1) * μ + 2 * μ / 3 + (t : ℝ) * (μ / 3)
      ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + D + ∑ g ∈ S, p g) :
    Nonempty (Canonical w p μ (2 * μ / 3) k R D) := by
  classical
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  set ε : ℝ := μ / 3 with hεdef
  have hε : 0 ≤ ε := by simp only [hεdef]; linarith
  have hvbS : ∀ g ∈ S, vbar w p g = p g := by
    intro g hg; exact max_eq_left (hS2 g hg)
  -- move goods of `S` into the large goods until every part has one, or nothing is left to sell
  obtain ⟨S₁, hS₁sub, hS₁card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := min (k + t - A.card) S.card)
      (le_trans (min_le_right _ _) le_rfl)
  set A' : Finset G := A ∪ S₁ with hA'def
  set S' : Finset G := S \ S₁ with hS'def
  have hA'S₁ : Disjoint A S₁ := Finset.disjoint_of_subset_right hS₁sub hAS
  have hA'card : A'.card = A.card + min (k + t - A.card) S.card := by
    rw [hA'def, Finset.card_union_of_disjoint hA'S₁, hS₁card]
  have hA'le : A'.card ≤ k + t := by
    rw [hA'card]; omega
  have hA'seed : A'.card = k + t ∨ S' = ∅ := by
    rcases le_total (k + t - A.card) S.card with h | h
    · left; rw [hA'card, min_eq_left h]; omega
    · right
      have : S₁ = S := Finset.eq_of_subset_of_card_le hS₁sub (by rw [hS₁card, min_eq_right h])
      simp [hS'def, this]
  have hRA' : A' ∪ C ∪ S' ⊆ R := by
    intro x hx
    rw [hRdef]
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
        · exact Finset.mem_union_right _ (hS₁sub hx)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1
  have hSsplit : (∑ g ∈ S₁, p g) + (∑ g ∈ S', p g) = ∑ g ∈ S, p g := by
    rw [hS'def, Finset.sum_sdiff_eq_sub hS₁sub]; ring
  have hA'sum : (∑ g ∈ A', vbar w p g) = (∑ g ∈ A, vbar w p g) + ∑ g ∈ S₁, p g := by
    rw [hA'def, Finset.sum_union hA'S₁]
    congr 1
    exact Finset.sum_congr rfl (fun g hg => hvbS g (hS₁sub hg))
  -- run the filling procedure
  obtain ⟨F⟩ := fill_exists_pairs w p hp hε t (k - 1) A' C S' D 0 none
    (by
      intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · exact hA1 g hg
      · rw [hvbS g (hS₁sub hg)]; exact hS1 g (hS₁sub hg))
    (by
      intro g hg
      have : g ∈ R := hRA' (Finset.mem_union_left _ (Finset.mem_union_left _ hg))
      have := hsmall g this
      simp only [hεdef]; linarith)
    (by intro g hg; simpa [hεdef] using hC1 g hg)
    (fun g hg => hS1 g (Finset.mem_sdiff.mp hg).1)
    (fun g hg => hvbS g (Finset.mem_sdiff.mp hg).1)
    (Finset.disjoint_union_left.mpr ⟨hAC, Finset.disjoint_of_subset_left hS₁sub hCS.symm⟩)
    (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_of_subset_right Finset.sdiff_subset hAS,
      Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx)⟩)
    (Finset.disjoint_of_subset_right Finset.sdiff_subset hCS)
    hD (Or.inl rfl) (by simp) (fun _ => rfl)
    (by omega)
    (by
      rcases hA'seed with h | h
      · left; omega
      · right; exact ⟨h, rfl⟩)
    (by
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hk
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast, hA'sum]
      simp only [hεdef] at hbud ⊢
      have h3 : (3 : ℝ) * (μ / 3) = μ := by ring
      rw [h3]
      linarith [hbud, hSsplit])
  -- package the result
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at F
  refine ⟨{ goods := fun j => F.goods (j : ℕ)
            sell := F.sell
            src := fun j => F.src (j : ℕ)
            dcash := fun j => F.dcash (j : ℕ)
            scash := fun j => F.scash (j : ℕ)
            goods_subset := fun j => (F.goods_subset j).trans hRA'
            goods_disj := ?_
            sell_subset := ?_
            sell_disj := fun j => F.sell_disj _
            src_mem := fun j f hf => F.src_mem _ f hf
            dcash_nonneg := fun j => F.dcash_nonneg _
            scash_nonneg := fun j => F.scash_nonneg _
            dcash_sum := ?_
            scash_sum := ?_
            scash_zero := fun j hj => F.scash_zero _ hj
            price_large := ?_
            acceptable := ?_
            pure_or_singleton := ?_
            singleton_dcash := ?_
            singleton_cond := ?_ }⟩
  · intro j j' hjj
    exact F.goods_disj _ _ (fun h => hjj (Fin.val_injective h))
  · intro x hx
    have hx' := F.sell_subset hx
    simp only [Option.toFinset_none, Finset.union_empty] at hx'
    exact hRA' hx'
  · rw [Fin.sum_univ_eq_sum_range (fun j => F.dcash j) k]
    exact F.dcash_sum
  · intro f _
    have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin k => F.src (j : ℕ) = some f),
          F.scash (j : ℕ)
        = ∑ j ∈ (Finset.range k).filter (fun j => F.src j = some f), F.scash j := by
      rw [Finset.sum_filter, Finset.sum_filter,
        Fin.sum_univ_eq_sum_range (fun j => if F.src j = some f then F.scash j else 0) k]
    rw [h1]
    simpa using F.scash_sum f
  · intro f hf
    have := F.price_large f hf
    simp only [hεdef] at this
    linarith
  · intro j
    have := F.acceptable (j : ℕ) j.isLt
    simp only [hεdef] at this
    linarith
  · intro j hj
    exact F.pure_or_singleton _ (by simpa using fun h => hj (Fin.val_injective (by simpa using h)))
      j.isLt
  · intro j hj
    exact F.singleton_dcash _ (by simpa using fun h => hj (Fin.val_injective (by simpa using h)))
  · intro j hj hsrc e he f hf
    have h1 := F.singleton_large (j : ℕ)
      (by simpa using fun h => hj (Fin.val_injective (by simpa using h))) hsrc e he
    have h2 := F.price_large f hf
    simp only [hεdef] at h1 h2
    linarith
end FairSelling
