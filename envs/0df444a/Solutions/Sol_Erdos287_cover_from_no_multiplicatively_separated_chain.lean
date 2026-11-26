-- Prove2me | solution 1 for Erdos287.cover_from_no_multiplicatively_separated_chain
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:04:06.778648+00:00
-- url     : https://prove2.me/submissions/30d66f00-247b-40e1-a960-27b539b6908d

import Mathlib

open Finset

set_option autoImplicit false

/-- If a finite set has no long multiplicatively separated sequence,
greedily selected elements cover it by a bounded number of intervals. -/
theorem solution (S : Finset ℕ) (R k : ℕ)
    (hno : ¬ ∃ f : ℕ → ℕ, (∀ i < k + 1, f i ∈ S) ∧
      (∀ i < k, R * f i ≤ f (i + 1))) :
    ∃ C : Finset ℕ, C ⊆ S ∧ C.card ≤ k ∧
      S ⊆ C.biUnion (fun m => Finset.Ico m (R * m)) := by
  induction k generalizing S with
  | zero =>
    have hS : S = ∅ := by
      by_contra hne
      obtain ⟨m, hm⟩ := nonempty_iff_ne_empty.mpr hne
      exact hno ⟨fun _ => m, fun _ _ => hm, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    subst S
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    by_cases hS : S.Nonempty
    · let m := S.min' hS
      have hm : m ∈ S := min'_mem S hS
      let T := S.filter (fun n => R * m ≤ n)
      have hT : T ⊆ S := filter_subset _ _
      have hTno : ¬ ∃ f : ℕ → ℕ, (∀ i < k + 1, f i ∈ T) ∧
          (∀ i < k, R * f i ≤ f (i + 1)) := by
        rintro ⟨f, hf, hseq⟩
        let g : ℕ → ℕ
          | 0 => m
          | n + 1 => f n
        refine hno ⟨g, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => exact hm
          | succ i => exact hT (hf i (by omega))
        · intro i hi
          cases i with
          | zero => exact (mem_filter.mp (hf 0 (by omega))).2
          | succ i => exact hseq i (by omega)
      obtain ⟨C, hCT, hcard, hcov⟩ := ih T hTno
      refine ⟨insert m C, insert_subset hm (hCT.trans hT), ?_, ?_⟩
      · exact (card_insert_le m C).trans (Nat.add_le_add_right hcard 1)
      · intro x hx
        by_cases hxt : R * m ≤ x
        · obtain ⟨c, hc, hx'⟩ := mem_biUnion.mp (hcov (mem_filter.mpr ⟨hx, hxt⟩))
          exact mem_biUnion.mpr ⟨c, mem_insert_of_mem hc, hx'⟩
        · have hmx : m ≤ x := min'_le S x hx
          exact mem_biUnion.mpr ⟨m, mem_insert_self _ _, mem_Ico.mpr ⟨hmx, lt_of_not_ge hxt⟩⟩
    · have hS' := not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨∅, by simp, by simp, by simp⟩

