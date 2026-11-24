-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.TaylorLogMetric.logarithm_series_coefficient_identities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:07.238993+00:00
-- url     : https://prove2.me/submissions/5aede420-7c0c-4d17-b8a0-ee40b9be3689

import Definitions.Def_Formalism_LogVandermondeBounds_EvenOddPowerQuotientEqualityCases
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefL_pow
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefL_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefG_pow
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefG_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefA_pow
import Theorems.Thm_Formalism_LogVandermondeBounds_TaylorLogMetric_coefA_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.TaylorLogMetric
open Finset
namespace Formalism.LogVandermondeBounds.TaylorLogMetric
theorem _root_.solution : LogarithmSeriesIdentities := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  constructor
  · intro a
    by_cases hd : p ∣ a
    · obtain ⟨c, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p c), Nat.mul_div_cancel_left c hp0]
      have ha1 : p * c ≠ 1 := by
        intro h
        rcases c with _ | c
        · simp at h
        · nlinarith
      rw [if_neg ha1, sub_zero]
      by_cases hc : ∃ k, c = p * (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hc
        rw [coefG_pow p k hp2, show p * (p * (p ^ 2) ^ k) = (p ^ 2) ^ (k + 1) by ring, coefL_pow p _ hp2]
      · rw [coefG_zero p c hc, coefL_zero]
        rintro ⟨j, hj⟩
        rcases j with _ | k
        · rw [pow_zero] at hj
          exact ha1 hj
        · apply hc
          refine ⟨k, ?_⟩
          have : p * c = p * (p * (p ^ 2) ^ k) := by rw [hj]; ring
          exact Nat.eq_of_mul_eq_mul_left hp0 this
    · rw [if_neg hd]
      by_cases ha : a = 1
      · subst ha
        have h1 := coefL_pow p 0 hp2
        rw [pow_zero, pow_zero] at h1
        rw [if_pos rfl, h1]
        norm_num
      · rw [if_neg ha, sub_zero, coefL_zero]
        rintro ⟨j, rfl⟩
        rcases j with _ | k
        · exact ha (pow_zero _)
        · exact hd (dvd_pow (dvd_pow_self p two_ne_zero) (Nat.succ_ne_zero k))
  · intro a b
    by_cases hA : ∃ i, a = p * (p ^ 2) ^ i
    · obtain ⟨i, rfl⟩ := hA
      rw [coefG_pow p i hp2]
      by_cases hB : ∃ k, b = (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hB
        simp only [coefB]
        rw [coefL_pow p k hp2, coefA_pow p k i hp2]
        rcases k with _ | j
        · have hn : ¬(p ∣ p * (p ^ 2) ^ i ∧ p ∣ (p ^ 2) ^ 0) := by
            rintro ⟨-, h⟩
            rw [pow_zero, Nat.dvd_one] at h
            omega
          rw [if_neg hn, if_pos (Nat.zero_le _)]
          field_simp
          ring
        · have hb : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j) := by ring
          rw [hb, if_pos ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hp0,
            Nat.mul_div_cancel_left _ hp0, coefA_pow p i j hp2]
          by_cases h : i ≤ j
          · rw [if_pos h, if_neg (by omega)]
            field_simp
            ring
          · rw [if_neg h, if_pos (by omega)]
            field_simp
            ring
      · simp only [coefB]
        rw [coefL_zero p b hB, coefA_zero p b _ (by rintro ⟨i', j', -, h2, -⟩; exact hB ⟨i', h2⟩)]
        simp only [mul_zero, sub_zero]
        split_ifs with h
        · obtain ⟨-, c, rfl⟩ := h
          rw [Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0]
          apply coefA_zero
          rintro ⟨i', j', -, -, h3⟩
          exact hB ⟨j' + 1, by rw [h3]; ring⟩
        · rfl
    · simp only [coefB]
      rw [coefG_zero p a hA, coefA_zero p b a (by rintro ⟨i', j', -, -, h3⟩; exact hA ⟨j', h3⟩)]
      simp only [zero_mul, zero_sub, mul_zero, neg_zero]
      split_ifs with h
      · obtain ⟨⟨c, rfl⟩, -⟩ := h
        rw [Nat.mul_div_cancel_left _ hp0]
        apply coefA_zero
        rintro ⟨i', j', -, h2, -⟩
        exact hA ⟨i', by rw [h2]⟩
      · rfl
end Formalism.LogVandermondeBounds.TaylorLogMetric
