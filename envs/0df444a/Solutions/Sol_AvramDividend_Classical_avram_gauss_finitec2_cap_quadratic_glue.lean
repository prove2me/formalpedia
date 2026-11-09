-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_finitec2_cap_quadratic_glue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:45:04.87508+00:00
-- url     : https://prove2.me/submissions/3f1146e9-49ea-466b-85f8-9f8215ce7a28

import Mathlib.Analysis.Convex.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- A quadratic upper Taylor estimate glued to the cap-linear extension.
    It covers a starting reserve equal to the cap with no cap derivative. -/
theorem solution
    (w : ℝ → ℝ) (u C L : ℝ) (huC : u < C) (hL : 0 ≤ L)
    (hgrad : ∀ s ∈ Ico u C, 1 ≤ deriv w s)
    (hquad : ∀ s ∈ Ico u C, ∀ t ∈ Icc u C,
      w t ≤ w s + deriv w s * (t - s) + L / 2 * (t - s) ^ 2)
    (hgrowth : ∀ t ∈ Icc u C, C - t ≤ w C - w t) :
    let V : ℝ → ℝ := fun y => if y ≤ C then w y else w C + (y - C)
    let g : ℝ → ℝ := fun y => if y < C then deriv w y else 1
    ∀ s t : ℝ, u ≤ s → u ≤ t →
      V t ≤ V s + g s * (t - s) + L / 2 * (t - s) ^ 2 := by
  dsimp
  intro s t hs ht
  by_cases hsc : s < C
  · have hscle : s ≤ C := hsc.le
    by_cases htc : t ≤ C
    · simpa only [if_pos htc, if_pos hscle, if_pos hsc] using
        (hquad s ⟨hs, hsc⟩ t ⟨ht, htc⟩)
    · have hct : C < t := lt_of_not_ge htc
      have hband := hquad s ⟨hs, hsc⟩ C ⟨huC.le, le_rfl⟩
      have hg := hgrad s ⟨hs, hsc⟩
      have hpos : 0 ≤ t - C := sub_nonneg.mpr hct.le
      have hprod : t - C ≤ deriv w s * (t - C) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hg hpos
      have hmul : 0 ≤ (t - C) * (C - s) :=
        mul_nonneg hpos (sub_nonneg.mpr hscle)
      have hsq : (C - s) ^ 2 ≤ (t - s) ^ 2 := by
        nlinarith [sq_nonneg (t - C), hmul]
      have hq : L / 2 * (C - s) ^ 2 ≤ L / 2 * (t - s) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hL (by norm_num))
      simp only [if_neg htc, if_pos hscle, if_pos hsc]
      nlinarith [hband, hprod, hq]
  · have hcs : C ≤ s := le_of_not_gt hsc
    have hvs : (if s ≤ C then w s else w C + (s - C)) =
        w C + (s - C) := by
      by_cases hscle : s ≤ C
      · have heq : s = C := le_antisymm hscle hcs
        subst s
        simp
      · simp [hscle]
    have hqnonneg : 0 ≤ L / 2 * (t - s) ^ 2 :=
      mul_nonneg (div_nonneg hL (by norm_num)) (sq_nonneg _)
    by_cases htc : t ≤ C
    · have hdiff := hgrowth t ⟨ht, htc⟩
      simp only [if_pos htc, if_neg hsc, hvs]
      linarith
    · simp only [if_neg htc, if_neg hsc, hvs]
      linarith
