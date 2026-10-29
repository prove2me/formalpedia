-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_ENNReal_factor_crossmul_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:16:27.770054+00:00
-- url     : https://prove2.me/submissions/0ba98302-3a5b-4373-a528-0f86e1f968ca

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_Reflection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact positive finite-rate ENNReal product equations imply the real
cross-multiplied factor, without dividing any infinite expectation. -/
theorem solution
    (T B K : ENNReal) (a b p lam L : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p)
    (hlam : 0 < lam) (hL : 0 ≤ L)
    (hFactor : T = B * K)
    (hTerminal : ENNReal.ofReal a * T = ENNReal.ofReal p)
    (hSup : ENNReal.ofReal b * B = ENNReal.ofReal lam)
    (hLap : K = ENNReal.ofReal L) :
    L * a = (p / lam) * b := by
  have hENN :
      ENNReal.ofReal (a * lam * L) = ENNReal.ofReal (p * b) := by
    calc
      _ = (ENNReal.ofReal a * ENNReal.ofReal lam) *
            ENNReal.ofReal L := by
              rw [ENNReal.ofReal_mul (mul_nonneg ha.le hlam.le),
                ENNReal.ofReal_mul ha.le]
      _ = (ENNReal.ofReal a * (ENNReal.ofReal b * B)) * K := by
              rw [hSup, hLap]
      _ = (ENNReal.ofReal a * (B * K)) * ENNReal.ofReal b := by
              ac_rfl
      _ = (ENNReal.ofReal a * T) * ENNReal.ofReal b := by
              rw [← hFactor]
      _ = ENNReal.ofReal p * ENNReal.ofReal b := by
              rw [hTerminal]
      _ = ENNReal.ofReal (p * b) :=
              (ENNReal.ofReal_mul hp.le).symm
  have hReal : a * lam * L = p * b :=
    (ENNReal.ofReal_eq_ofReal_iff
      (mul_nonneg (mul_nonneg ha.le hlam.le) hL)
      (mul_nonneg hp.le hb.le)).mp hENN
  have hLamNe : lam ≠ 0 := ne_of_gt hlam
  have hDiv : L * a = (p * b) / lam :=
    (eq_div_iff hLamNe).2 (by nlinarith [hReal])
  calc
    L * a = (p * b) / lam := hDiv
    _ = (p / lam) * b := by ring
