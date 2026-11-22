-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_neighborhood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:40.471973+00:00
-- url     : https://prove2.me/submissions/b6230759-1994-48be-bba8-db0403783367

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_hDist_embed0_embed0
public import Theorems.Thm_BooleanIsoperimetry_hDist_embed0_embed1
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice0 (neighborhood 1 A) = neighborhood 1 (slice0 A) ∪ slice1 A := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, huA, hu⟩ : ∃ u ∈ A, hDist u (embed0 x) ≤ 1 := by
      unfold slice0 at hx; unfold neighborhood at hx; aesop
    by_cases hlast : Fin.last n ∈ u
    · -- If Fin.last n ∈ u, write u = embed1 w with w ∈ slice1 A.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed1 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp only [embed1, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨ fun hi => or_iff_not_imp_left.mpr fun hi' =>
          ⟨ ⟨ i.val, lt_of_le_of_ne (Fin.le_last _) (by simpa [Fin.ext_iff] using hi') ⟩,
            by simpa [Fin.ext_iff] using hi, rfl ⟩,
          fun hi => hi.elim (fun hi => hi.symm ▸ hlast)
            fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha ⟩
      have h_dist : hDist (embed1 w) (embed0 x) = hDist w x + 1 := by
        convert hDist_embed0_embed1 x w using 1
        · exact congr_arg Finset.card (by ext; simp +decide [symmDiff_comm])
        · unfold hDist; simp +decide [symmDiff_comm]
      simp_all +decide only [hDist, Finset.mem_union, mem_neighborhood_iff,
        add_le_iff_nonpos_left, nonpos_iff_eq_zero, Finset.card_eq_zero,
        Finset.symmDiff_eq_empty, symmDiff_self, Finset.bot_eq_empty,
        Finset.card_empty, zero_add]
      exact Or.inr (Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩)
    · -- Since $Fin.last n \notin u$, we can write $u = embed0 w$ for some $w \in Cube n$.
      obtain ⟨w, hw⟩ : ∃ w : Cube n, u = embed0 w := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ u)
        ext i; simp [embed0]
        induction i using Fin.lastCases <;> aesop
      simp_all +decide only [hDist_embed0_embed0, Finset.mem_union, mem_neighborhood_iff]
      exact Or.inl ⟨ w, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, huA ⟩, hu ⟩
  · simp only [neighborhood, slice0, Finset.mem_filter, Finset.mem_univ, true_and,
      slice1, Finset.mem_union]
    rintro (⟨ u, hu, hu' ⟩ | hu)
    · exact ⟨ _, hu, by rwa [hDist_embed0_embed0] ⟩
    · refine ⟨_, hu, ?_⟩
      simp +decide [hDist, embed0, embed1]
      simp +decide [symmDiff]
end BooleanIsoperimetry
