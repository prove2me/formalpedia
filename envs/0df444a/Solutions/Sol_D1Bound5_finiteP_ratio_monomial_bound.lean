-- Prove2me | solution 1 for D1Bound5.finiteP_ratio_monomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:52:43.904149+00:00
-- url     : https://prove2.me/submissions/ae679739-54ac-4ae3-898b-a96d8f46b324

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

section
namespace D1Bound5

/-- The ratio-sensitive monomial bound used by the finite P rows. The
exponent certificates are checked on the actual finite coefficient tables.
No analytic or polynomial-height bound occurs as a hypothesis. -/
theorem _root_.solution (A B S : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (r : Fin 3) (i j l m t e : ℕ)
    (htotal : i+j+l+t ≤ m+2)
    (he : e+j+l = if r=0 then 2 else m+2)
    (hl : r ≠ 2 → l ≤ 2) :
    A^i*B^j*S^l/(![A,B,S] r)^m ≤ (S^2/A^t)*(A/B)^e := by
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := hA0.trans_le hAB
  have hS0 : 0 < S := hB0.trans_le hBS
  have hB : 1 ≤ B := hA.trans hAB
  have hS : 1 ≤ S := hB.trans hBS
  have hroot : 0 < ![A,B,S] r := by fin_cases r <;> assumption
  have hden : 0 < A^t*B^e := by positivity
  have heq : (S^2/A^t)*(A/B)^e = (S^2*A^e)/(A^t*B^e) := by
    rw [div_pow]
    ring
  rw [heq]
  apply (div_le_div_iff₀ (pow_pos hroot m) hden).mpr
  have hlhs : (A^i*B^j*S^l)*(A^t*B^e) = A^(i+t)*B^(j+e)*S^l := by
    simp only [pow_add]
    ring
  rw [hlhs]
  fin_cases r
  · simp only [Matrix.cons_val_zero] at *
    norm_num at he
    have he' : j+e+l = 2 := by omega
    have hpow : i+t ≤ m+e := by omega
    have hBS' : B^(j+e)*S^l ≤ S^2 := by
      calc
        _ ≤ S^(j+e)*S^l := by gcongr
        _ = S^2 := by rw [← pow_add,he']
    calc
      A^(i+t)*B^(j+e)*S^l = A^(i+t)*(B^(j+e)*S^l) := by ring
      _ ≤ A^(m+e)*S^2 := by gcongr
      _ = (S^2*A^e)*A^m := by rw [pow_add]; ring
  · simp only [Matrix.cons_val_succ,Matrix.cons_val_zero] at *
    norm_num at he
    have hl' : l ≤ 2 := hl (by decide)
    have hpow : i+t ≤ e := by omega
    have hidx : j+e = m+(2-l) := by omega
    have hidx2 : 2-l+l = 2 := by omega
    have hBS' : B^(2-l)*S^l ≤ S^2 := by
      calc
        _ ≤ S^(2-l)*S^l := by gcongr
        _ = S^2 := by rw [← pow_add,hidx2]
    calc
      A^(i+t)*B^(j+e)*S^l = A^(i+t)*B^m*(B^(2-l)*S^l) := by rw [hidx,pow_add]; ring
      _ ≤ A^e*B^m*S^2 := by gcongr
      _ = (S^2*A^e)*B^m := by ring
  · simp only [Matrix.cons_val_succ,Matrix.cons_val_zero] at *
    norm_num at he
    have hpow : i+t ≤ e := by omega
    have he' : j+e+l = m+2 := by omega
    have hBS' : B^(j+e)*S^l ≤ S^(m+2) := by
      calc
        _ ≤ S^(j+e)*S^l := by gcongr
        _ = S^(m+2) := by rw [← pow_add,he']
    calc
      A^(i+t)*B^(j+e)*S^l = A^(i+t)*(B^(j+e)*S^l) := by ring
      _ ≤ A^e*S^(m+2) := by gcongr
      _ = (S^2*A^e)*S^m := by rw [pow_add]; ring

end D1Bound5
end
