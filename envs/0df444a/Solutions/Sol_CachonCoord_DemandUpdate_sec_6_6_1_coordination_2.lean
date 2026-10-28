-- Prove2me | solution 2 for CachonCoord.DemandUpdate.sec_6_6_1_coordination
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:32:10.858134+00:00
-- url     : https://prove2.me/submissions/723f9a34-eafb-425e-b2c0-0a519f180cd2

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits
import Theorems.Thm_CachonCoord_DemandUpdate_p65_retailer_period2
import Theorems.Thm_CachonCoord_DemandUpdate_p66_retailer_period1
import Theorems.Thm_CachonCoord_DemandUpdate_p67_margin

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open CachonCoord.DemandUpdate
open Model

-- carved from submission 2a6179e2-1b5b-4dcc-8cd3-a69b92f744fa, lines 513-539

theorem solution (M : Model) (lam w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) ∧
    (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 = lam * M.Omega1 q2sel q1) ∧
    (∀ q1, 0 ≤ q1 → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1) ∧
    (0 < lam → ∀ q1, 0 ≤ q1 → IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1) ∧
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by
  obtain ⟨r1, r2, r3⟩ := CachonCoord.DemandUpdate.p65_retailer_period2 M lam w2 b hlam0 hlam1 hb hw2
  obtain ⟨_, h⟩ := CachonCoord.DemandUpdate.p66_retailer_period1 M lam w1 w2 b q2sel hq2 hlam0 hlam1 hb hw2
  obtain ⟨a1, a2, a3⟩ := h hw1
  obtain ⟨m1, m2, m3⟩ := CachonCoord.DemandUpdate.p67_margin M lam w1 w2 b hlam0 hlam1 hb hw2 hw1
  exact ⟨r1, r2, r3, a1, a2, a3, m1, m2, m3⟩
