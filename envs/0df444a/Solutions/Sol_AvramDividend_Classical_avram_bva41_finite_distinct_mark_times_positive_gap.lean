-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva41_finite_distinct_mark_times_positive_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:27:46.890758+00:00
-- url     : https://prove2.me/submissions/be251fec-6f85-4f7b-89da-9173258821d5

import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical

/-- A finite set of physical jump times has a common positive spacing. -/
theorem solution (S : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ |s - t| := by
  classical
  let R : Finset ℝ :=
    ((S.product S).filter (fun p => p.1 ≠ p.2)).image (fun p => |p.1 - p.2|)
  by_cases hR : R.Nonempty
  · have hPositive : ∀ v ∈ R, 0 < v := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
      have hpNe : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact abs_pos.mpr (sub_ne_zero.mpr hpNe)
    refine ⟨R.min' hR, hPositive (R.min' hR) (Finset.min'_mem R hR), ?_⟩
    intro s hs t ht hne
    apply Finset.min'_le
    exact Finset.mem_image.mpr
      ⟨(s, t), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, ht⟩, hne⟩, rfl⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro s hs t ht hne
    exfalso
    apply hR
    exact ⟨|s - t|, Finset.mem_image.mpr
      ⟨(s, t), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hs, ht⟩, hne⟩, rfl⟩⟩
