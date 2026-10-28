-- Prove2me | solution 1 for D1Bound5.fixed_cutoff_start_above_Q
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:44.493717+00:00
-- url     : https://prove2.me/submissions/39725a34-fc50-489c-b941-0be06de60f87

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
namespace D1Bound5





/-- Scalar conversion of the first overlap, retaining every strict
inequality. The two growth premises are precisely the actual retained
bounds already proved for fixed triples. -/
theorem _root_.solution (K S T C D : ℝ)
    (hK : 0 < K) (hS : 0 < S) (hT : 0 < T) (hC : 0 < C)
    (hgap : K*T^5/S^2 < C) (hstart : C^7/(S^2*T^4) < D)
    (hover : 1 < (1-1/4000 : ℝ)*K^4*T^10/(12100*S^10)) :
    4*55^2*T^6*C^3/(1-1/4000 : ℝ) < D := by
  have hc : K*T^5 < C*S^2 := (div_lt_iff₀ (pow_pos hS 2)).mp hgap
  have hc4 : (K*T^5)^4 < (C*S^2)^4 := by gcongr
  have hp : K^4*T^20 < C^4*S^8 := by convert hc4 using 1 <;> ring
  have he : 0 < (1-1/4000 : ℝ) := by norm_num
  have hn : 12100*S^10 < (1-1/4000 : ℝ)*K^4*T^10 := by
    have h := (lt_div_iff₀ (by positivity : (0 : ℝ) < 12100*S^10)).mp hover
    simpa only [one_mul] using h
  have hprod : (12100*S^10)*T^10 < (1-1/4000 : ℝ)*(C^4*S^8) := by
    calc
      _ < ((1-1/4000 : ℝ)*K^4*T^10)*T^10 :=
        mul_lt_mul_of_pos_right hn (pow_pos hT 10)
      _ = (1-1/4000 : ℝ)*(K^4*T^20) := by ring
      _ < _ := mul_lt_mul_of_pos_left hp he
  have hC4 : 12100*S^2*T^10 < (1-1/4000 : ℝ)*C^4 := by
    apply (mul_lt_mul_iff_of_pos_right (pow_pos hS 8)).mp
    calc
      (12100*S^2*T^10)*S^8 = (12100*S^10)*T^10 := by ring
      _ < (1-1/4000 : ℝ)*(C^4*S^8) := hprod
      _ = ((1-1/4000 : ℝ)*C^4)*S^8 := by ring
  have hlower : 4*55^2*T^6*C^3/(1-1/4000 : ℝ) < C^7/(S^2*T^4) := by
    apply (div_lt_div_iff₀ he (by positivity : 0 < S^2*T^4)).mpr
    have hh := mul_lt_mul_of_pos_right hC4 (pow_pos hC 3)
    convert hh using 1 <;> ring
  exact hlower.trans hstart

end D1Bound5
end
