-- Prove2me | solution 1 for GDPRPrivacy.ProfitGain.propA3_profit_higher_small_alpha
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:23:38.556453+00:00
-- url     : https://prove2.me/submissions/9ea12079-281b-4147-9bbf-af943aaef55b

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_ProfitGain_profit_difference_J
import Theorems.Thm_GDPRPrivacy_ProfitGain_J_pos

set_option autoImplicit false

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ pHat →
      IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ pTilde →
      GDPRPrivacy.PriceRise.profitBefore x α pHat < GDPRPrivacy.PriceRise.profitAfter x α pTilde := by
  have h1 : α < (1 - 2 * x) / 2 := by
    have h := hα1
    unfold GDPRPrivacy.PriceRise.alpha1 at h
    rcases le_total ((1 - 2 * x) / 2) 0 with hc | hc
    · rw [max_eq_right hc] at h; linarith
    · rwa [max_eq_left hc] at h
  have hxh : x < 1 / 2 := by linarith
  obtain ⟨e1, e2, e3⟩ := GDPRPrivacy.ProfitGain.profit_difference_J x α hx0 hx1 hα hα1
  refine ⟨e1, e2, fun pHat pTilde hHat hTilde => ?_⟩
  have hd := e3 pHat pTilde hHat hTilde
  have hJ := GDPRPrivacy.ProfitGain.J_pos x α hx0 hxh hα h1
  linarith
