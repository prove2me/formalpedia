-- Prove2me | solution 1 for FairSelling.servable_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:59.691368+00:00
-- url     : https://prove2.me/submissions/5a5fb640-3048-4957-9630-7a4009da7653

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (j : Fin n) (hj : j ∈ T) (B F₀ : Finset G) (a : ℝ)
    (hB : B ⊆ R) (hF₀ : F₀ ⊆ R) (hBF : Disjoint B F₀)
    (ha : 0 ≤ a) (hserve : τ j ≤ vbarSum (v j) p B + a)
    (hrec : Servable v p τ (T.erase j) (R \ (B ∪ F₀)) (D + (∑ g ∈ F₀, p g) - a)) :
    Servable v p τ T R D := by
  classical
  obtain ⟨A', F', q', hA'R, hF'R, hA'disj, hF'disj, hq'0, hq'sum, hq'serve, hq'out⟩ := hrec
  have hjout := hq'out j (Finset.notMem_erase j T)
  refine ⟨Function.update A' j B, F' ∪ F₀, Function.update q' j a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = j
    · subst h; simpa using hB
    · rw [Function.update_of_ne h]
      exact Finset.Subset.trans (hA'R i) Finset.sdiff_subset
  · exact Finset.union_subset (Finset.Subset.trans hF'R Finset.sdiff_subset) hF₀
  · intro i k hik
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self, Function.update_of_ne (Ne.symm hik)]
      exact Finset.disjoint_left.mpr (fun x hxB hxA => by
        have := hA'R k hxA
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inl hxB))
    · by_cases hk : k = j
      · subst hk
        rw [Function.update_self, Function.update_of_ne hi]
        exact Finset.disjoint_right.mpr (fun x hxB hxA => by
          have := hA'R i hxA
          simp only [Finset.mem_sdiff, Finset.mem_union] at this
          exact this.2 (Or.inl hxB))
      · rw [Function.update_of_ne hi, Function.update_of_ne hk]
        exact hA'disj i k hik
  · intro i
    by_cases hi : i = j
    · subst hi
      rw [Function.update_self]
      refine Finset.disjoint_left.mpr (fun x hx hxB => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · have := hF'R hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inl hxB)
      · exact Finset.disjoint_left.mp hBF hxB hx
    · rw [Function.update_of_ne hi]
      refine Finset.disjoint_left.mpr (fun x hx hxA => ?_)
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.disjoint_left.mp (hF'disj i) hx hxA
      · have := hA'R i hxA
        simp only [Finset.mem_sdiff, Finset.mem_union] at this
        exact this.2 (Or.inr hx)
  · intro i
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact ha
    · rw [Function.update_of_ne hi]; exact hq'0 i
  · have hsum : ∑ i, Function.update q' j a i = (∑ i, q' i) - q' j + a := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
      have : ∑ i ∈ Finset.univ \ {j}, q' i = (∑ i, q' i) - q' j := by
        rw [eq_sub_iff_add_eq, Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
        simp
      rw [this]; ring
    have hFsum : ∑ g ∈ F' ∪ F₀, p g = (∑ g ∈ F', p g) + ∑ g ∈ F₀, p g := by
      refine Finset.sum_union ?_
      refine Finset.disjoint_left.mpr (fun x hx hx₀ => ?_)
      have := hF'R hx
      simp only [Finset.mem_sdiff, Finset.mem_union] at this
      exact this.2 (Or.inr hx₀)
    rw [hsum, hFsum, hjout.2]
    linarith [hq'sum]
  · intro i hi
    by_cases h : i = j
    · subst h; rw [Function.update_self, Function.update_self]; exact hserve
    · rw [Function.update_of_ne h, Function.update_of_ne h]
      exact hq'serve i (Finset.mem_erase.mpr ⟨h, hi⟩)
  · intro i hi
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Function.update_of_ne hij, Function.update_of_ne hij]
    exact hq'out i (fun h => hi (Finset.mem_of_mem_erase h))
end FairSelling
