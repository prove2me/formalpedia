-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.oaD_price_gap
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:29:20.647299+00:00
-- url     : https://prove2.me/submissions/07f4edc4-68bf-4897-b6cf-81bec356993a

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_PriceRise_oaA1_max_before
import Theorems.Thm_GDPRPrivacy_PriceRise_oaA2_max_after
import Theorems.Thm_GDPRPrivacy_PriceRise_alpha1_le_alpha2

open GDPRPrivacy.PriceRise

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) :
    (∃ p, IsMaxOn (profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde : ℝ,
      IsMaxOn (profitBefore x α) Set.univ pHat →
      IsMaxOn (profitAfter x α) Set.univ pTilde →
        (α < alpha1 x →
          pTilde - pHat = (2 + 8 * α - x * (4 + 6 * α - 3 * x)) / 12) ∧
        (alpha1 x ≤ α → α < alpha2 x →
          pTilde - pHat = (14 + 4 * α + 3 * x ^ 2 - 8 * x - 6 * x * α - 4 * beta x α) / 12) ∧
        (alpha2 x ≤ α →
          pTilde - pHat = (Gamma x α - beta x α) / 3) := by
  have hA := oaA1_max_before x α hx0 hx1 hα
  have hB := oaA2_max_after x α hx0 hx1 hα
  have h12 := alpha1_le_alpha2 x hx0 hx1
  refine ⟨⟨_, (hA _).2 rfl⟩, ⟨_, (hB _).2 rfl⟩, fun pHat pTilde hH hT => ?_⟩
  have eH := (hA pHat).1 hH
  have eT := (hB pTilde).1 hT
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h2 => ?_⟩
  · rw [if_pos h1] at eH; rw [if_pos (lt_of_lt_of_le h1 h12)] at eT
    rw [eH, eT]; ring
  · rw [if_neg (not_lt.2 h1)] at eH; rw [if_pos h2] at eT
    rw [eH, eT]; ring
  · rw [if_neg (not_lt.2 (le_trans h12 h2))] at eH; rw [if_neg (not_lt.2 h2)] at eT
    rw [eH, eT]; ring
