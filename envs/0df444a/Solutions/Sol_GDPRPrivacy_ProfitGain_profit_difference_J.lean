-- Prove2me | solution 1 for GDPRPrivacy.ProfitGain.profit_difference_J
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T13:17:49.747829+00:00
-- url     : https://prove2.me/submissions/06e6ca85-a4ff-4969-ab09-a21417d5de99

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_PriceRise_alpha1_le_alpha2
import Theorems.Thm_GDPRPrivacy_ProfitGain_profit_before_case1a
import Theorems.Thm_GDPRPrivacy_ProfitGain_profit_after_case2a

set_option autoImplicit false

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α)
    (hα1 : α < GDPRPrivacy.PriceRise.alpha1 x) :
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ p) ∧
    (∃ p, IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ p) ∧
    ∀ pHat pTilde, IsMaxOn (GDPRPrivacy.PriceRise.profitBefore x α) Set.univ pHat →
      IsMaxOn (GDPRPrivacy.PriceRise.profitAfter x α) Set.univ pTilde →
      GDPRPrivacy.PriceRise.profitAfter x α pTilde - GDPRPrivacy.PriceRise.profitBefore x α pHat =
        (76 + 27 * x ^ 4 - 96 * α - 32 * α ^ 2 * (3 + α)
            + 12 * x ^ 2 * (1 + α) * (1 + 9 * α)) / 432
          - (4 * x ^ 3 * (8 + 27 * α) + 24 * x * (4 + 4 * α ^ 2 - α)) / 432 := by
  have hα2 : α < GDPRPrivacy.PriceRise.alpha2 x :=
    lt_of_lt_of_le hα1 (GDPRPrivacy.PriceRise.alpha1_le_alpha2 x hx0 hx1)
  obtain ⟨hb1, hb2⟩ := GDPRPrivacy.ProfitGain.profit_before_case1a x α hx0 hx1 hα hα1
  obtain ⟨ha1, ha2⟩ := GDPRPrivacy.ProfitGain.profit_after_case2a x α hx0 hx1 hα hα2
  refine ⟨hb1, ha1, fun pHat pTilde hHat hTilde => ?_⟩
  rw [hb2 pHat hHat, ha2 pTilde hTilde]
  ring
