-- Prove2me | solution 1 for FairSelling.servable_extend_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:27.010584+00:00
-- url     : https://prove2.me/submissions/ce8b9205-ce32-447c-8f46-215d287df7c1

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (Kset : Finset (Fin n)) (hKT : Kset ⊆ T)
    (bundle : Fin n → Finset G) (F : Finset G) (cash : Fin n → ℝ)
    (hb : ∀ k ∈ Kset, bundle k ⊆ R) (hF : F ⊆ R)
    (hbdisj : ∀ k ∈ Kset, ∀ l ∈ Kset, k ≠ l → Disjoint (bundle k) (bundle l))
    (hbF : ∀ k ∈ Kset, Disjoint F (bundle k))
    (hcash0 : ∀ k ∈ Kset, 0 ≤ cash k)
    (hserve : ∀ k ∈ Kset, τ k ≤ vbarSum (v k) p (bundle k) + cash k)
    (hrec : Servable v p τ (T \ Kset) (R \ (Kset.biUnion bundle ∪ F))
              (D + (∑ g ∈ F, p g) - ∑ k ∈ Kset, cash k)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨A', F', q', hA'R, hF'R, hA'disj, hF'disj, hq'0, hq'sum, hq'serve, hq'out⟩ := hrec
  refine ⟨fun k => if k ∈ Kset then bundle k else A' k, F' ∪ F,
    fun k => if k ∈ Kset then cash k else q' k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]; exact hb k hk
    · simp only [if_neg hk]
      exact (hA'R k).trans Finset.sdiff_subset
  · exact Finset.union_subset (hF'R.trans Finset.sdiff_subset) hF
  · intro k l hkl
    by_cases hk : k ∈ Kset <;> by_cases hl : l ∈ Kset
    · simp only [if_pos hk, if_pos hl]; exact hbdisj k hk l hl hkl
    · simp only [if_pos hk, if_neg hl]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have := hA'R l hx'
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
      exact this.2 (Or.inl ⟨k, hk, hx⟩)
    · simp only [if_neg hk, if_pos hl]
      refine Finset.disjoint_right.mpr (fun x hx hx' => ?_)
      have := hA'R k hx'
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
      exact this.2 (Or.inl ⟨l, hl, hx⟩)
    · simp only [if_neg hk, if_neg hl]; exact hA'disj k l hkl
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · have := hF'R hx
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion] at this
        exact this.2 (Or.inl ⟨k, hk, hx'⟩)
      · exact Finset.disjoint_left.mp (hbF k hk) hx hx'
    · simp only [if_neg hk]
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (hF'disj k) hx hx'
      · have := hA'R k hx'
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inr hx)
  · intro k
    by_cases hk : k ∈ Kset
    · simp only [if_pos hk]; exact hcash0 k hk
    · simp only [if_neg hk]; exact hq'0 k
  · have hsplit : ∑ k, (if k ∈ Kset then cash k else q' k)
        = (∑ k ∈ Kset, cash k) + ∑ k ∈ Finset.univ \ Kset, q' k := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Kset), add_comm]
      congr 1
      · exact Finset.sum_congr rfl (fun k hk => by simp [hk])
      · exact Finset.sum_congr rfl (fun k hk => by simp [(Finset.mem_sdiff.mp hk).2])
    have hq'zero : ∀ k ∈ Kset, q' k = 0 := by
      intro k hk
      exact (hq'out k (by simp [Finset.mem_sdiff, hk])).2
    have hq'univ : ∑ k ∈ Finset.univ \ Kset, q' k = ∑ k, q' k := by
      rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
      have : ∑ k ∈ Kset, q' k = 0 := Finset.sum_eq_zero hq'zero
      rw [this]; ring
    have hFunion : ∑ g ∈ F' ∪ F, p g = (∑ g ∈ F', p g) + ∑ g ∈ F, p g := by
      refine Finset.sum_union ?_
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have := hF'R hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at this
      exact this.2 (Or.inr hx')
    rw [hsplit, hq'univ, hFunion]
    linarith [hq'sum]
  · intro k hk
    by_cases hkK : k ∈ Kset
    · simp only [if_pos hkK]; exact hserve k hkK
    · simp only [if_neg hkK]
      exact hq'serve k (Finset.mem_sdiff.mpr ⟨hk, hkK⟩)
  · intro k hk
    have hkK : k ∉ Kset := fun h => hk (hKT h)
    simp only [if_neg hkK]
    exact hq'out k (fun h => hk (Finset.mem_sdiff.mp h).1)
end FairSelling
