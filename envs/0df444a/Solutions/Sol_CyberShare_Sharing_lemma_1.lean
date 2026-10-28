-- Prove2me | solution 1 for CyberShare.Sharing.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:46:18.40568+00:00
-- url     : https://prove2.me/submissions/ae2261b7-3302-445d-a4f0-cab4dfcb6c4f

import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace Aux_CyberW31

lemma core (a b k1 k2 c1 c2 p1 p2 : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (ha1 : c1 < a) (ha2 : c2 < a) :
    (c1 ≤ p1 ∧ c2 ≤ p2 ∧
      (∀ x, c1 ≤ x → (x - c1) * (a - x + b * p2) - k1 ≤ (p1 - c1) * (a - p1 + b * p2) - k1) ∧
      (∀ x, c2 ≤ x → (x - c2) * (a - x + b * p1) - k2 ≤ (p2 - c2) * (a - p2 + b * p1) - k2)) ↔
    (p1 = (2 * (a + c1) + b * (a + c2)) / (4 - b ^ 2) ∧
      p2 = (2 * (a + c2) + b * (a + c1)) / (4 - b ^ 2)) := by
  have h4 : 0 < 4 - b ^ 2 := by nlinarith
  have h4ne : 4 - b ^ 2 ≠ 0 := h4.ne'
  constructor
  · rintro ⟨hp1, hp2, ho1, ho2⟩
    have hv1 : c1 ≤ (a + b * p2 + c1) / 2 := by nlinarith [mul_nonneg hb0 (hc2.trans hp2)]
    have hv2 : c2 ≤ (a + b * p1 + c2) / 2 := by nlinarith [mul_nonneg hb0 (hc1.trans hp1)]
    have hs1 : (p1 - (a + b * p2 + c1) / 2) ^ 2 ≤ 0 := by nlinarith [ho1 _ hv1]
    have hs2 : (p2 - (a + b * p1 + c2) / 2) ^ 2 ≤ 0 := by nlinarith [ho2 _ hv2]
    have e1 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hs1 (sq_nonneg _))
    have e2 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hs2 (sq_nonneg _))
    constructor
    · rw [eq_div_iff h4ne]; linear_combination 4 * e1 + 2 * b * e2
    · rw [eq_div_iff h4ne]; linear_combination 4 * e2 + 2 * b * e1
  · rintro ⟨h1, h2⟩
    have e1 : 2 * p1 = a + b * p2 + c1 := by rw [h1, h2]; field_simp; ring
    have e2 : 2 * p2 = a + b * p1 + c2 := by rw [h1, h2]; field_simp; ring
    have hp1n : 0 ≤ p1 := by rw [h1]; apply div_nonneg _ h4.le; nlinarith
    have hp2n : 0 ≤ p2 := by rw [h2]; apply div_nonneg _ h4.le; nlinarith
    refine ⟨by nlinarith [mul_nonneg hb0 hp2n], by nlinarith [mul_nonneg hb0 hp1n],
      fun x _ => ?_, fun x _ => ?_⟩
    · nlinarith [sq_nonneg (x - p1)]
    · nlinarith [sq_nonneg (x - p2)]

end Aux_CyberW31

open CyberShare.Sharing in
theorem solution (P : Params) (hP : P.Standing) (attack1 attack2 : Bool)
    (K1 K2 p1 p2 : ℝ) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    IsPriceEq P attack1 attack2 K1 K2 p1 p2 ↔
      p1 = pStar P attack1 attack2 K1 K2 ∧
      p2 = pStar P attack2 attack1 K2 K1 := by
  obtain ⟨⟨hc, hg, -, -, -, -, -, -, -, -, -⟩, hb0, hb1, hd, hcd, -⟩ := hP
  have hcost : ∀ (att : Bool) (K : ℝ), 0 ≤ K → 0 ≤ cost P att K ∧ cost P att K < P.a := by
    intro att K hK
    have hpos0 : 0 ≤ pos (P.delta - P.gamma * K) := le_max_right _ _
    have hposd : pos (P.delta - P.gamma * K) ≤ P.delta :=
      max_le (by nlinarith [mul_nonneg hg.le hK]) hd.le
    cases att
    · simp only [cost, Bool.false_eq_true, if_false]; constructor <;> linarith
    · simp only [cost, if_true]; constructor <;> linarith
  obtain ⟨hc1, ha1⟩ := hcost attack1 K1 hK1
  obtain ⟨hc2, ha2⟩ := hcost attack2 K2 hK2
  unfold IsPriceEq profit
  rw [Aux_CyberW31.core P.a P.b _ _ _ _ p1 p2 hb0 hb1 hc1 hc2 ha1 ha2]
  have h2b : (2 - P.b) ≠ 0 := by intro h; linarith
  have h2b' : (2 + P.b) ≠ 0 := by intro h; linarith
  have h4 : (4 - P.b ^ 2) ≠ 0 := by intro h; nlinarith
  have hF1 : (2 * (P.a + cost P attack1 K1) + P.b * (P.a + cost P attack2 K2)) / (4 - P.b ^ 2)
      = pStar P attack1 attack2 K1 K2 := by
    cases attack1 <;> cases attack2 <;>
      simp only [cost, pStar, Bool.false_eq_true, if_true, if_false, add_zero] <;>
      field_simp <;> ring
  have hF2 : (2 * (P.a + cost P attack2 K2) + P.b * (P.a + cost P attack1 K1)) / (4 - P.b ^ 2)
      = pStar P attack2 attack1 K2 K1 := by
    cases attack1 <;> cases attack2 <;>
      simp only [cost, pStar, Bool.false_eq_true, if_true, if_false, add_zero] <;>
      field_simp <;> ring
  rw [hF1, hF2]
