-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.lemmaA3_equilibrium_pairs
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:37:56.200192+00:00
-- url     : https://prove2.me/submissions/42c9a3c6-9617-4ea5-9717-c063f4f167b6

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
        (x ≤ 1 / 2 → α < alpha1 x →
          (x < pHat ∧ pHat < 1 + x) ∧ (x < pTilde ∧ pTilde < 1 + x)) ∧
        (x ≤ 2 - Real.sqrt 2 → alpha1 x ≤ α → α < alpha2 x →
          (x - 1 ≤ pHat ∧ pHat ≤ x) ∧ (x < pTilde ∧ pTilde < 1 + x)) ∧
        (x ≤ 1 → alpha2 x ≤ α →
          (x - 1 ≤ pHat ∧ pHat ≤ x) ∧ (0 ≤ pTilde ∧ pTilde ≤ x)) := by
  have hA := oaA1_max_before x α hx0 hx1 hα
  have hB := oaA2_max_after x α hx0 hx1 hα
  have h12 := alpha1_le_alpha2 x hx0 hx1
  refine ⟨⟨_, (hA _).2 rfl⟩, ⟨_, (hB _).2 rfl⟩, fun pHat pTilde hH hT => ?_⟩
  have eH := (hA pHat).1 hH
  have eT := (hB pTilde).1 hT
  have hb0 : 0 ≤ beta x α := Real.sqrt_nonneg _
  have hbsq : beta x α ^ 2 = 6 + (x + α - 1) ^ 2 := Real.sq_sqrt (by positivity)
  have hbabs : |x + α - 1| < beta x α :=
    (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; linarith)
  have hG0 : 0 ≤ Gamma x α := Real.sqrt_nonneg _
  have hGsq : Gamma x α ^ 2 = 6 + (2 - 2 * x + α) ^ 2 := Real.sq_sqrt (by positivity)
  have hGabs : |2 - 2 * x + α| < Gamma x α :=
    (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; linarith)
  -- facts on the candidates
  have candHi : α < alpha1 x → x < (1 + x - 2 * α) / 3 ∧ (1 + x - 2 * α) / 3 < 1 + x := by
    intro hA1
    have h1 : 2 * x + 2 * α < 1 := by
      unfold alpha1 at hA1
      rcases max_cases ((1 - 2 * x) / 2) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA1 <;> linarith
    constructor <;> linarith
  have candHl : alpha1 x ≤ α → x - 1 ≤ (2 * (x - 1) - α + beta x α) / 3 ∧
      (2 * (x - 1) - α + beta x α) / 3 ≤ x := by
    intro hA1
    have h1 : 1 ≤ 2 * x + 2 * α := by have := le_trans (le_max_left _ _) hA1; linarith
    have hb1 : x + α - 1 < beta x α := lt_of_le_of_lt (le_abs_self _) hbabs
    have hb2 : beta x α ≤ x + 2 + α :=
      (pow_le_pow_iff_left₀ hb0 (by linarith) two_ne_zero).1 (by nlinarith)
    constructor <;> linarith
  have candTh : α < alpha2 x → x < (2 * (1 - α * x) + x ^ 2) / 4 ∧
      (2 * (1 - α * x) + x ^ 2) / 4 < 1 + x := by
    intro hA2
    have h2 : 2 * x * α < 2 - 4 * x + x ^ 2 := by
      unfold alpha2 at hA2
      rcases max_cases ((2 - 4 * x + x ^ 2) / (2 * x)) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA2
      · rw [lt_div_iff₀ (by positivity)] at hA2; linarith
      · linarith
    constructor <;> nlinarith [mul_nonneg hα hx0.le]
  have candTl : alpha2 x ≤ α → 0 ≤ (Gamma x α - (2 - 2 * x + α)) / 3 ∧
      (Gamma x α - (2 - 2 * x + α)) / 3 ≤ x := by
    intro hA2
    have h2 : 2 - 4 * x + x ^ 2 ≤ 2 * x * α := by
      have := le_trans (le_max_left _ _) hA2
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have hG1 : 2 - 2 * x + α < Gamma x α := lt_of_le_of_lt (le_abs_self _) hGabs
    have hG2 : Gamma x α ≤ 2 + x + α :=
      (pow_le_pow_iff_left₀ hG0 (by linarith) two_ne_zero).1 (by nlinarith)
    constructor <;> linarith
  refine ⟨fun _ h1 => ?_, fun _ h1 h2 => ?_, fun _ h2 => ?_⟩
  · rw [if_pos h1] at eH; rw [if_pos (lt_of_lt_of_le h1 h12)] at eT
    rw [eH, eT]; exact ⟨candHi h1, candTh (lt_of_lt_of_le h1 h12)⟩
  · rw [if_neg (not_lt.2 h1)] at eH; rw [if_pos h2] at eT
    rw [eH, eT]; exact ⟨candHl h1, candTh h2⟩
  · rw [if_neg (not_lt.2 (le_trans h12 h2))] at eH; rw [if_neg (not_lt.2 h2)] at eT
    rw [eH, eT]; exact ⟨candHl (le_trans h12 h2), candTl h2⟩
