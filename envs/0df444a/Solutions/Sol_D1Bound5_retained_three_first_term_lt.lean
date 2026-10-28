-- Prove2me | solution 1 for D1Bound5.retained_three_first_term_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:15.957598+00:00
-- url     : https://prove2.me/submissions/bd06eff1-39df-4456-8816-655b6d6a049c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- Exact scalar control of the first summand in the retained three-anchor
form. This combines the proved strong two-anchor gap with the terminal-root
lower bound, retaining the normalized Vandermonde parameter. -/
theorem _root_.solution
    (A B S T C W Q : ℝ) (hA : 0 < A) (hB : 0 < B) (hS : 0 < S)
    (hW : 0 < W) (hQ : 0 < Q)
    (hfront : 2*A*B*S < T)
    (hstrong : B^2*T^3 < (10001/10000 : ℝ)*C)
    (hroot : (3999/4000 : ℝ)*T*C < W^2) :
    51*(Q*B*S^2)/(100*W) < (51051/400000 : ℝ)*Q/(A^2*B^2) := by
  have hT : 0 < T := (by positivity : 0 < 2*A*B*S).trans hfront
  have hsq : (2*A*B*S)^2 < T^2 := by
    have h := mul_pos (sub_pos.mpr hfront) (by positivity : 0 < T+2*A*B*S)
    nlinarith only [h]
  have hfour : (2*A*B*S)^4 < T^4 := by
    have h := mul_pos (sub_pos.mpr hsq)
      (by positivity : 0 < T^2+(2*A*B*S)^2)
    nlinarith only [h]
  have hfront' := mul_lt_mul_of_pos_left hfour (pow_pos hB 2)
  have hstrong' := mul_lt_mul_of_pos_left hstrong hT
  have hstrong'' := mul_lt_mul_of_pos_left hstrong' (by norm_num : (0:ℝ)<3999/4000)
  have hroot' := mul_lt_mul_of_pos_left hroot (by norm_num : (0:ℝ)<10001/10000)
  have hfront'' := mul_lt_mul_of_pos_left hfront' (by norm_num : (0:ℝ)<3999/4000)
  let x := A^2*B^3*S^2
  have hx : 0 < x := by dsimp [x]; positivity
  have hbound : (16*(3999/4000) : ℝ)*x^2 < (10001/10000 : ℝ)*W^2 := by
    dsimp [x]
    nlinarith only [hfront'', hstrong'', hroot']
  have hsquare : ((4000/1001 : ℝ)*x)^2 < W^2 := by
    nlinarith only [hbound, sq_nonneg x]
  have hlarge : (4000/1001 : ℝ)*x < W := by
    by_contra h
    have hle : W ≤ (4000/1001 : ℝ)*x := le_of_not_gt h
    have hp := mul_nonneg (sub_nonneg.mpr hle)
      (by positivity : 0 ≤ (4000/1001 : ℝ)*x+W)
    nlinarith only [hp, hsquare]
  apply (div_lt_div_iff₀ (by positivity : 0 < 100*W)
    (by positivity : 0 < A^2*B^2)).2
  have hmul := mul_lt_mul_of_pos_left hlarge
    (by positivity : 0 < (100*(51051/400000 : ℝ))*Q)
  dsimp [x] at hmul
  nlinarith only [hmul]



end D1Bound5
end
