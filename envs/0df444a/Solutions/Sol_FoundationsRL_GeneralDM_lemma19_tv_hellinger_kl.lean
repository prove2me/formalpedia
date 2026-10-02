-- Prove2me | solution 1 for FoundationsRL.GeneralDM.lemma19_tv_hellinger_kl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:17:45.260889+00:00
-- url     : https://prove2.me/submissions/95076587-a2db-4f54-8a8f-fb09e45db6a3

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

set_option autoImplicit false

namespace FoundationsRL.GeneralDM

lemma eaa_tv_le_hel {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1) :
    (totalVariationDiscrete P Q) ^ 2 ≤ hellingerSq P Q := by
  unfold totalVariationDiscrete hellingerSq
  have hpt : ∀ y, |P y - Q y| =
      |Real.sqrt (P y) - Real.sqrt (Q y)| * (Real.sqrt (P y) + Real.sqrt (Q y)) := by
    intro y
    have h1 := Real.sq_sqrt (hP.1 y)
    have h2 := Real.sq_sqrt (hQ.1 y)
    have h3 : 0 ≤ Real.sqrt (P y) + Real.sqrt (Q y) := by positivity
    rw [← abs_of_nonneg h3, ← abs_mul]
    congr 1
    nlinarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun y => |Real.sqrt (P y) - Real.sqrt (Q y)|) (fun y => Real.sqrt (P y) + Real.sqrt (Q y))
  simp only [← hpt, sq_abs] at hcs
  have hb : ∑ y, (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 ≤ 4 := by
    have : ∀ y, (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 ≤ 2 * P y + 2 * Q y := by
      intro y
      have h1 := Real.sq_sqrt (hP.1 y)
      have h2 := Real.sq_sqrt (hQ.1 y)
      nlinarith [sq_nonneg (Real.sqrt (P y) - Real.sqrt (Q y))]
    calc ∑ y, (Real.sqrt (P y) + Real.sqrt (Q y)) ^ 2 ≤ ∑ y, (2 * P y + 2 * Q y) :=
          Finset.sum_le_sum fun y _ => this y
      _ = 4 := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP.2, hQ.2]; norm_num
  have hH : 0 ≤ ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2 :=
    Finset.sum_nonneg fun y _ => sq_nonneg _
  nlinarith

lemma eaa_pt {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q = 0 → p = 0) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ p * Real.log (p / q) + (q - p) := by
  have h1 := Real.sq_sqrt hp
  have h2 := Real.sq_sqrt hq
  rcases hp.lt_or_eq with hp' | hp'
  · have hq' : 0 < q := by
      rcases hq.lt_or_eq with h | h
      · exact h
      · exact absurd (hpq h.symm) hp'.ne'
    set a := Real.sqrt p with ha
    set b := Real.sqrt q with hb
    have ha0 : 0 < a := Real.sqrt_pos.2 hp'
    have hb0 : 0 < b := Real.sqrt_pos.2 hq'
    have hlog : Real.log (p / q) = 2 * Real.log (a / b) := by
      rw [← h1, ← h2, ← div_pow, Real.log_pow]; norm_num
    have hl := Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb0)
    rw [inv_div] at hl
    have key : a ^ 2 * (1 - b / a) = a ^ 2 - a * b := by field_simp
    rw [hlog, ← h1, ← h2]
    nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg a)]
  · subst hp'
    simp
    rw [h2]

end FoundationsRL.GeneralDM

open FoundationsRL.GeneralDM in
theorem solution {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1) :
    ENNReal.ofReal ((totalVariationDiscrete P Q) ^ 2) ≤ ENNReal.ofReal (hellingerSq P Q) ∧
    ENNReal.ofReal (hellingerSq P Q) ≤ klDivDiscrete P Q := by
  refine ⟨ENNReal.ofReal_le_ofReal (eaa_tv_le_hel P Q hP hQ), ?_⟩
  unfold klDivDiscrete
  split_ifs with hac
  · apply ENNReal.ofReal_le_ofReal
    unfold hellingerSq
    calc ∑ y, (Real.sqrt (P y) - Real.sqrt (Q y)) ^ 2
        ≤ ∑ y, (P y * Real.log (P y / Q y) + (Q y - P y)) :=
          Finset.sum_le_sum fun y _ => eaa_pt (hP.1 y) (hQ.1 y) (hac y)
      _ = ∑ y, P y * Real.log (P y / Q y) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hP.2, hQ.2]; ring
  · exact le_top
