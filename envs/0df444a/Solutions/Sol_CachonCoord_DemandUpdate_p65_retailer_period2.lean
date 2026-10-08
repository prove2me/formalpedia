-- Prove2me | solution 1 for CachonCoord.DemandUpdate.p65_retailer_period2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:05:22.071734+00:00
-- url     : https://prove2.me/submissions/b43f7b9c-f12d-4ebf-9da5-f47c338f87d9

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory


namespace CachonCoord.DemandUpdate

open Model

theorem p65_retailer_period2_core (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) := by
  have hid : ∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 =
      lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1 := by
    intro q1 ξ q2
    unfold Model.retailerProfit2 Model.Omega2
    rw [hb, hw2]; ring
  refine ⟨hid, ?_, ?_⟩
  · intro q1 ξ q2 h y hy
    have := h hy
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [hid, hid]; nlinarith
  · intro hl q1 ξ q2 h y hy
    have := h hy
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [hid, hid] at this
    have : lam * M.Omega2 q1 ξ y ≤ lam * M.Omega2 q1 ξ q2 := by linarith
    exact le_of_mul_le_mul_left this hl

end CachonCoord.DemandUpdate

open CachonCoord.DemandUpdate


theorem solution (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) := by
  exact p65_retailer_period2_core M lam w2 b hlam0 hlam1 hb hw2
