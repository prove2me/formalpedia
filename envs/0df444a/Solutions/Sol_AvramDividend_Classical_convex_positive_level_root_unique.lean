-- Prove2me | solution 1 for AvramDividend.Classical.convex_positive_level_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:58:47.776982+00:00
-- url     : https://prove2.me/submissions/f121d46c-6d9a-4c0c-a960-90268c9b4368

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Strictly positive levels of a convex function vanishing at zero
    have at most one positive preimage. -/
theorem solution
    (f : ℝ → ℝ) (q φ₁ φ₂ : ℝ)
    (hq : 0 < q) (hφ₁ : 0 < φ₁) (hφ₂ : 0 < φ₂)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0)
    (hroot₁ : f φ₁ = q) (hroot₂ : f φ₂ = q) :
    φ₁ = φ₂ := by
  have hcontr (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
      (hab : a < b) (hra : f a = q) (hrb : f b = q) : False := by
    have hma : a ∈ (Ici (0 : ℝ)) \ {0} := by
      simp only [mem_diff, mem_Ici, mem_singleton_iff]
      exact ⟨ha.le, ne_of_gt ha⟩
    have hmb : b ∈ (Ici (0 : ℝ)) \ {0} := by
      simp only [mem_diff, mem_Ici, mem_singleton_iff]
      exact ⟨hb.le, ne_of_gt hb⟩
    have hmono := hconv.slope_mono (by simp : (0 : ℝ) ∈ Ici 0)
    have hs : slope f 0 a ≤ slope f 0 b := hmono hma hmb hab.le
    have hsa : slope f 0 a = q / a := by
      rw [slope_def_field, hzero, hra]
      ring
    have hsb : slope f 0 b = q / b := by
      rw [slope_def_field, hzero, hrb]
      ring
    rw [hsa, hsb] at hs
    have hfrac : q / b < q / a :=
      (div_lt_div_iff₀ hb ha).2 (mul_lt_mul_of_pos_left hab hq)
    exact (not_lt_of_ge hs) hfrac
  rcases lt_trichotomy φ₁ φ₂ with hlt | heq | hgt
  · exact False.elim (hcontr φ₁ φ₂ hφ₁ hφ₂ hlt hroot₁ hroot₂)
  · exact heq
  · exact False.elim (hcontr φ₂ φ₁ hφ₂ hφ₁ hgt hroot₂ hroot₁)
