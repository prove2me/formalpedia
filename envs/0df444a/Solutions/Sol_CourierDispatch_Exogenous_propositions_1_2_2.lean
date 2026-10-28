-- Prove2me | solution 2 for CourierDispatch.Exogenous.propositions_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:05.673316+00:00
-- url     : https://prove2.me/submissions/90445a69-53be-435a-a8d8-14142bd008af

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting
import Theorems.Thm_CourierDispatch_Exogenous_unique_root
import Theorems.Thm_CourierDispatch_Exogenous_wait_difference_eq

-- carved verbatim out of submission b360cf71-fb45-484b-93df-4180182d9c81, lines 154-198

section
open CourierDispatch.Exogenous

theorem solution (CB : ℝ) (hCB : CBRange CB) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < TD ∧
      ∀ r lam : ℝ, 0 < r → 0 < lam → lam*r < TD →
        (WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam*r < a₁) ∧
        (WB r lam (muB r) CB < WD lam (muD r) CD ↔ a₁ < lam*r) ∧
        (∀ (Q : ℝ → ℝ) (Lam c : ℝ), 0 < Lam → lam ≤ Lam*r^2 → 0 < c →
          (V Q Lam r c lam (WB r lam (muB r) CB) < V Q Lam r c lam (WD lam (muD r) CD) ↔
            lam*r < a₁) ∧
          (V Q Lam r c lam (WD lam (muD r) CD) < V Q Lam r c lam (WB r lam (muB r) CB) ↔
            a₁ < lam*r)) := by
  obtain ⟨a,ha,haT,_,_,hz,hneg,hpos⟩ := CourierDispatch.Exogenous.unique_root CB hCB
  have hn (x : ℝ) (hx : 0 < x) (hxT : x < TD) : fA CB x < 0 ↔ x < a := by
    constructor
    · intro hf
      rcases lt_trichotomy x a with h | h | h
      · exact h
      · rw [h,hz] at hf; exact (lt_irrefl _ hf).elim
      · have hh := hpos x h hxT; linarith only [hf,hh]
    · exact hneg x hx
  have hp (x : ℝ) (hx : 0 < x) (hxT : x < TD) : 0 < fA CB x ↔ a < x := by
    constructor
    · intro hf
      rcases lt_trichotomy x a with h | h | h
      · have hh := hneg x hx h; linarith only [hf,hh]
      · rw [h,hz] at hf; exact (lt_irrefl _ hf).elim
      · exact h
    · exact fun h => hpos x h hxT
  refine ⟨a,ha,haT,?_⟩
  intro r lam hr hlam hstab
  have hdiff := CourierDispatch.Exogenous.wait_difference_eq CB r lam hr hlam hstab
  have h1 : WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam*r<a := by
    rw [← sub_neg,hdiff,div_lt_iff₀ hlam,zero_mul]
    exact hn (lam*r) (mul_pos hlam hr) hstab
  have h2 : WB r lam (muB r) CB < WD lam (muD r) CD ↔ a<lam*r := by
    rw [← sub_pos,hdiff,lt_div_iff₀ hlam,zero_mul]
    exact hp (lam*r) (mul_pos hlam hr) hstab
  refine ⟨h1,h2,?_⟩
  intro Q Lam c _ _ hc
  have hrev (x y : ℝ) : V Q Lam r c lam x < V Q Lam r c lam y ↔ y < x := by
    unfold V
    rw [mul_lt_mul_iff_right₀ hlam,sub_lt_sub_iff_left,mul_lt_mul_iff_right₀ hc]
  exact ⟨(hrev _ _).trans h1,(hrev _ _).trans h2⟩

end
