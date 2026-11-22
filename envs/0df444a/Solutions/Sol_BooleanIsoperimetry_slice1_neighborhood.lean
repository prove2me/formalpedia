-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:41.10885+00:00
-- url     : https://prove2.me/submissions/756b5567-4f67-48b4-a848-a88aa75edb6a

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_hDist_embed1_embed1
public import Theorems.Thm_BooleanIsoperimetry_hDist_embed0_embed1
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice1 (neighborhood 1 A) = neighborhood 1 (slice1 A) ∪ slice0 A := by
  ext v
  constructor
  · intro hv
    obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, hDist u (embed1 v) ≤ 1 := by
      unfold slice1 at hv; aesop
    by_cases hlast : Fin.last n ∈ u
    · -- If Fin.last n ∈ u, write u = embed1 w with w ∈ slice1 A.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed1 w := by
        use Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ u)
        ext i
        simp only [embed1, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨ fun hi =>
          if hi' : i = Fin.last n then Or.inl hi' else
            Or.inr ⟨ ⟨ i.val,
              lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using hi') ⟩,
              by simpa [Fin.ext_iff] using hi, rfl ⟩,
          fun hi => hi.elim (fun hi => hi.symm ▸ hlast)
            fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      simp_all +decide only [hDist_embed1_embed1, Finset.mem_union, mem_neighborhood_iff]
      exact Or.inl ⟨ w, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩, hu ⟩
    · -- Since $Fin.last n \notin u$, we can write $u = embed0 w$ for some $w \in Cube n$.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed0 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp only [embed0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ fun hi => by cases i using Fin.lastCases <;> aesop,
          fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      simp_all +decide only [hDist_embed0_embed1, add_le_iff_nonpos_left,
        nonpos_iff_eq_zero, Finset.mem_union, mem_neighborhood_iff]
      simp_all +decide only [hDist, Finset.card_eq_zero, Finset.symmDiff_eq_empty]
      exact Or.inr (Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩)
  · simp +zetaDelta only [Finset.mem_union, mem_neighborhood_iff] at *
    rintro (⟨ u, hu, huv ⟩ | hv) <;>
      simp_all +decide only [slice0, slice1, Finset.mem_filter, Finset.mem_univ,
        true_and, neighborhood]
    · use embed1 u, hu; simp_all +decide [hDist_embed1_embed1]
    · use embed0 v, hv, by
        rw [hDist_embed0_embed1]; norm_num
        unfold hDist; aesop
end BooleanIsoperimetry
