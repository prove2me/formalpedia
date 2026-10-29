-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bf_new_ENNReal_factor_crossmul_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:17:39.749829+00:00
-- url     : https://prove2.me/submissions/8489bd59-06c4-4252-aa22-20ac63b20d0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    (T B K : ENNReal) (a b p lam L : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hlam : 0 < lam) (hL : 0 ≤ L)
    (hFactor : T = B * K)
    (hTerminal : ENNReal.ofReal a * T = ENNReal.ofReal p)
    (hSup : ENNReal.ofReal b * B = ENNReal.ofReal lam)
    (hLap : K = ENNReal.ofReal L) :
    L * a = (p / lam) * b := by
  have hBtop : B ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by simpa using hb)] at hSup
    exact ENNReal.ofReal_ne_top hSup.symm
  set β' := B.toReal with hβ'
  have hB : B = ENNReal.ofReal β' := (ENNReal.ofReal_toReal hBtop).symm
  have hβ0 : 0 ≤ β' := ENNReal.toReal_nonneg
  rw [hB, ← ENNReal.ofReal_mul hb.le] at hSup
  rw [hFactor, hB, hLap, ← ENNReal.ofReal_mul hβ0, ← ENNReal.ofReal_mul ha.le] at hTerminal
  have e1 : b * β' = lam := by
    have := congrArg ENNReal.toReal hSup
    rwa [ENNReal.toReal_ofReal (mul_nonneg hb.le hβ0), ENNReal.toReal_ofReal hlam.le] at this
  have e2 : a * (β' * L) = p := by
    have := congrArg ENNReal.toReal hTerminal
    rwa [ENNReal.toReal_ofReal (mul_nonneg ha.le (mul_nonneg hβ0 hL)),
      ENNReal.toReal_ofReal hp.le] at this
  rw [← e1]
  have hβpos : 0 < β' := by
    rcases eq_or_lt_of_le hβ0 with h | h
    · rw [← h] at e1; linarith
    · exact h
  field_simp
  nlinarith [e2]
