-- Prove2me | solution 1 for CopycatSI.h1_pos_and_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:33:43.737553+00:00
-- url     : https://prove2.me/submissions/2820345b-d8e8-4d72-9782-297b5f733fb0

import Mathlib
import Definitions.Def_CopycatSI_Model
import Definitions.Def_CopycatSI_Game
import Definitions.Def_CopycatSI_ClosedForms

namespace Aux_CopycatH1

open CopycatSI

noncomputable def A (β : ℝ) : ℝ := β * (1 - β) / (2 - β) ^ 2
noncomputable def B (β : ℝ) : ℝ := β * (17 - 13 * β) / (4 - 3 * β) ^ 2
noncomputable def F (β : ℝ) : ℝ := (1 - β) / (4 - 3 * β)

theorem bs_facts : 3 * betaStar ^ 2 + 5 * betaStar - 4 = 0 ∧ 0 < betaStar ∧ betaStar < 2 / 3 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 73 by norm_num)
  have h0 := Real.sqrt_nonneg 73
  unfold betaStar
  refine ⟨by linear_combination (1 / 12 : ℝ) * h, ?_, ?_⟩
  · have : 5 < Real.sqrt 73 := by nlinarith
    linarith
  · have : Real.sqrt 73 < 9 := by nlinarith
    linarith

theorem A_nonneg {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 2 / 3) : 0 ≤ A β := by
  unfold A
  apply div_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)

theorem B_nonneg {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 2 / 3) : 0 ≤ B β := by
  unfold B
  apply div_nonneg (mul_nonneg h0 (by linarith)) (sq_nonneg _)

theorem A_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 3) : A a ≤ A b := by
  unfold A
  have h1 : 0 < (2 - a) ^ 2 := by have : 0 < 2 - a := by linarith
                                  positivity
  have h2 : 0 < (2 - b) ^ 2 := by have : 0 < 2 - b := by linarith
                                  positivity
  rw [div_le_div_iff₀ h1 h2]
  have hQ : 0 ≤ 3 * a * b - 4 * a - 4 * b + 4 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 / 3 - a by linarith) (show (0:ℝ) ≤ 2 / 3 - b by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hab) hQ]

theorem B_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 3) : B a ≤ B b := by
  unfold B
  have h1 : 0 < (4 - 3 * a) ^ 2 := by have : 0 < 4 - 3 * a := by linarith
                                      positivity
  have h2 : 0 < (4 - 3 * b) ^ 2 := by have : 0 < 4 - 3 * b := by linarith
                                      positivity
  rw [div_le_div_iff₀ h1 h2]
  have hQ : 0 ≤ 159 * a * b - 208 * a - 208 * b + 272 := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 / 3 - a by linarith) (show (0:ℝ) ≤ 2 / 3 - b by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hab) hQ]

theorem F_strict {a b : ℝ} (hab : a < b) (hb : b ≤ 2 / 3) : F b < F a := by
  unfold F
  have h1 : 0 < 4 - 3 * a := by linarith
  have h2 : 0 < 4 - 3 * b := by linarith
  rw [div_lt_div_iff₀ h2 h1]
  nlinarith

theorem rep {β : ℝ} (h0 : 0 ≤ β) (hle : β ≤ 2 / 3) :
    h1 β = F β - Real.sqrt (A β * B β / 4) := by
  have ha : 0 < 1 - β := by linarith
  have hb : 0 < 2 - β := by linarith
  have hc : 0 < 4 - 3 * β := by linarith
  have hX : 0 ≤ (1 - β) / ((2 - β) * (4 - 3 * β)) * β / 2 := by
    apply div_nonneg _ (by norm_num)
    exact mul_nonneg (div_nonneg ha.le (mul_pos hb hc).le) h0
  have hsq : (1 - β) / ((2 - β) * (4 - 3 * β)) * β / 2 *
      Real.sqrt ((17 - 13 * β) / (1 - β)) = Real.sqrt (A β * B β / 4) := by
    rw [← Real.sqrt_sq hX, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    unfold A B
    field_simp <;> ring
  have hF : (1 - β) / ((2 - β) * (4 - 3 * β)) * (2 - β) = F β := by
    unfold F
    field_simp
  rw [← hsq, ← hF]
  unfold h1
  ring

end Aux_CopycatH1

open CopycatSI Aux_CopycatH1 in
theorem solution :
    (∀ β : ℝ, 0 ≤ β → β < betaStar → 0 < h1 β) ∧
    StrictAntiOn h1 (Set.Icc 0 betaStar) := by
  obtain ⟨hbs, hbs0, hbs1⟩ := bs_facts
  constructor
  · intro β h0 hlt
    have hle : β ≤ 2 / 3 := by linarith
    rw [rep h0 hle]
    have ha : 0 < 1 - β := by linarith
    have hb : 0 < 2 - β := by linarith
    have hc : 0 < 4 - 3 * β := by linarith
    have hFpos : 0 < F β := by unfold F; exact div_pos ha hc
    have hq : 3 * β ^ 2 + 5 * β - 4 < 0 := by
      nlinarith [mul_pos (show 0 < betaStar - β by linarith)
        (show 0 < 3 * β + 3 * betaStar + 5 by linarith)]
    have hkey : F β ^ 2 - A β * B β / 4 =
        (1 - β) * ((3 * β ^ 2 + 5 * β - 4) * (3 * β - 4)) /
          (4 * (2 - β) ^ 2 * (4 - 3 * β) ^ 2) := by
      unfold F A B
      field_simp <;> ring
    have hpos : 0 < (1 - β) * ((3 * β ^ 2 + 5 * β - 4) * (3 * β - 4)) /
          (4 * (2 - β) ^ 2 * (4 - 3 * β) ^ 2) := by
      apply div_pos
      · exact mul_pos ha (mul_pos_of_neg_of_neg hq (by linarith))
      · positivity
    have hlt2 : Real.sqrt (A β * B β / 4) < F β := by
      rw [Real.sqrt_lt' hFpos]
      linarith
    linarith
  · intro a ha b hb hab
    obtain ⟨ha0, ha1⟩ := ha
    obtain ⟨hb0, hb1⟩ := hb
    have ha2 : a ≤ 2 / 3 := by linarith
    have hb2 : b ≤ 2 / 3 := by linarith
    rw [rep ha0 ha2, rep hb0 hb2]
    have hF := F_strict hab hb2
    have hAB : A a * B a / 4 ≤ A b * B b / 4 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul (A_mono ha0 hab.le hb2) (B_mono ha0 hab.le hb2) (B_nonneg ha0 ha2)
        (A_nonneg hb0 hb2)
    have := Real.sqrt_le_sqrt hAB
    linarith
