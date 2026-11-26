-- Prove2me | solution 1 for Erdos287.near_target_mass_between_nested_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:29:19.555554+00:00
-- url     : https://prove2.me/submissions/0e6b43db-e434-4074-987f-a6a59587b149

import Mathlib

open Finset

set_option autoImplicit false

private theorem sum_just_above (U : Finset ℕ) (w : ℕ → ℚ) (W : ℚ) (hW : 0 < W)
    (hw : ∀ n ∈ U, w n ≤ W) (t : ℚ) (ht₀ : 0 ≤ t) (ht : t ≤ ∑ n ∈ U, w n) :
    ∃ A ⊆ U, t ≤ (∑ n ∈ A, w n) ∧ (∑ n ∈ A, w n) < t + W := by
  induction U using Finset.induction_on generalizing t with
  | empty =>
    have hz : t = 0 := le_antisymm (by simpa using ht) ht₀
    subst t
    exact ⟨∅, empty_subset _, by simp, by simpa using hW⟩
  | insert n U hn ih =>
    by_cases hz : t = 0
    · subst t
      exact ⟨∅, empty_subset _, by simp, by simpa using hW⟩
    have htpos : 0 < t := lt_of_le_of_ne ht₀ fun he => hz he.symm
    by_cases hfit : t ≤ w n
    · have hlt : w n < t + W := lt_of_le_of_lt (hw n (mem_insert_self _ _)) (by linarith)
      exact ⟨{n}, singleton_subset_iff.mpr (mem_insert_self _ _), by simpa using hfit,
        by simpa using hlt⟩
    · have hrem₀ : 0 ≤ t - w n := sub_nonneg.mpr (le_of_lt (lt_of_not_ge hfit))
      rw [sum_insert hn] at ht
      have hrem : t - w n ≤ ∑ k ∈ U, w k := by linarith
      obtain ⟨A, hAu, hl, hu⟩ := ih (fun k hk => hw k (mem_insert_of_mem hk))
        (t - w n) hrem₀ hrem
      have hna : n ∉ A := fun ha => hn (hAu ha)
      refine ⟨insert n A, insert_subset_insert _ hAu, ?_, ?_⟩
      · rw [sum_insert hna]
        linarith only [hl]
      · rw [sum_insert hna]
        linarith only [hu]

/-- A nested interval of retained configurations brackets any intervening
target from above, with error smaller than one optional term. -/
theorem solution (I H G : Finset ℕ) (w : ℕ → ℚ) (t W : ℚ)
    (hHG : H ⊆ G) (hGI : G ⊆ I) (hW : 0 < W)
    (hw : ∀ n ∈ G \ H, w n ≤ W)
    (hlo : (∑ n ∈ I \ G, w n) ≤ t) (hhi : t ≤ ∑ n ∈ I \ H, w n) :
    ∃ D : Finset ℕ, I \ G ⊆ D ∧ D ⊆ I \ H ∧
      t ≤ (∑ n ∈ D, w n) ∧ (∑ n ∈ D, w n) < t + W := by
  let B := I \ G
  let U := G \ H
  have hpart : B ∪ U = I \ H := by
    ext n
    constructor
    · intro hn
      rcases mem_union.mp hn with hb | hu
      · obtain ⟨hi, hg⟩ := mem_sdiff.mp hb
        exact mem_sdiff.mpr ⟨hi, fun hh => hg (hHG hh)⟩
      · obtain ⟨hg, hh⟩ := mem_sdiff.mp hu
        exact mem_sdiff.mpr ⟨hGI hg, hh⟩
    · intro hn
      obtain ⟨hi, hh⟩ := mem_sdiff.mp hn
      by_cases hg : n ∈ G
      · exact mem_union_right _ (mem_sdiff.mpr ⟨hg, hh⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hi, hg⟩)
  have hdisj : Disjoint B U := by
    exact disjoint_left.mpr fun _ hb hu => (mem_sdiff.mp hb).2 (mem_sdiff.mp hu).1
  let Bmass := ∑ n ∈ B, w n
  have hB : Bmass ≤ t := hlo
  have hU : t - Bmass ≤ ∑ n ∈ U, w n := by
    rw [← hpart, sum_union hdisj] at hhi
    change t ≤ Bmass + ∑ n ∈ U, w n at hhi
    linarith only [hhi]
  obtain ⟨A, hAU, ha₁, ha₂⟩ := sum_just_above U w W hW hw (t - Bmass) (sub_nonneg.mpr hB) hU
  have hA : Disjoint B A := hdisj.mono_right hAU
  refine ⟨B ∪ A, subset_union_left, ?_, ?_, ?_⟩
  · rw [← hpart]
    exact union_subset_union subset_rfl hAU
  · rw [sum_union hA]
    change t ≤ Bmass + ∑ n ∈ A, w n
    linarith only [ha₁]
  · rw [sum_union hA]
    change Bmass + ∑ n ∈ A, w n < t + W
    linarith only [ha₂]

