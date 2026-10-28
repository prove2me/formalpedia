-- Prove2me | solution 1 for D1Bound5.retained_three_h48_scalar_gap
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:45:42.900793+00:00
-- url     : https://prove2.me/submissions/879c549a-6b01-4a20-a0ff-d13a9edb3fd8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_retained_three_first_term_lt

section
namespace D1Bound5



/-- The H48 retained gap follows from the actual nonzero three-anchor form
estimate and the two terminal-root norm inequalities. No retained-gap
inequality or coarse growth conclusion is supplied as a hypothesis. -/
theorem _root_.solution
    (A B S T C W Q L : ℝ)
    (hA : 3 ≤ A) (hB : 3 ≤ B) (hS : 3 ≤ S) (hST : S ≤ T)
    (hW : 0 < W) (hQ : 0 < Q) (hQ8 : Q ≤ 8)
    (hfront : 2*A*B*S < T)
    (hstrong : B^2*T^3 < (10001/10000 : ℝ)*C)
    (hrootlo : (3999/4000 : ℝ)*T*C < W^2)
    (hroothi : W^2 ≤ T*C+1)
    (hL : 1 ≤ L)
    (hupper : L < 51*(Q*B*S^2)/(100*W) +
      (19/200 : ℝ)*(Q*B*S^2)*W/(A*B*S*T^3)) :
    ((9999/10000 : ℝ)*(200/19)^2) *
      (1/Q-(51051/400000 : ℝ)/(A^2*B^2))^2 *
        (A^2*T^5/S^2) < C := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hS0 : 0 < S := by linarith
  have hT0 : 0 < T := hS0.trans_le hST
  have hAn : A ≠ 0 := ne_of_gt hA0
  have hBn : B ≠ 0 := ne_of_gt hB0
  have hSn : S ≠ 0 := ne_of_gt hS0
  have hTn : T ≠ 0 := ne_of_gt hT0
  have hQn : Q ≠ 0 := ne_of_gt hQ
  have hAB : (81 : ℝ) ≤ A^2*B^2 := by
    calc
      (81 : ℝ) = 3^2*3^2 := by norm_num
      _ ≤ A^2*B^2 := by gcongr
  have hinv : (1/8 : ℝ) ≤ 1/Q := by
    apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<8) hQ).2
    simpa using hQ8
  have herr : (51051/400000 : ℝ)/(A^2*B^2) ≤ (51051/400000)/81 := by
    apply (div_le_div_iff₀ (by positivity : 0<A^2*B^2) (by norm_num : (0:ℝ)<81)).2
    nlinarith only [hAB]
  let alpha : ℝ := (200/19)*(1/Q-(51051/400000)/(A^2*B^2))
  have halpha : 1 < alpha := by dsimp [alpha]; nlinarith only [hinv, herr]
  have halpha0 : 0 < alpha := by linarith only [halpha]
  have hfirst := retained_three_first_term_lt A B S T C W Q
    hA0 hB0 hS0 hW hQ hfront hstrong hrootlo
  have hwindow : 1 < (51051/400000 : ℝ)*Q/(A^2*B^2) +
      (19/200 : ℝ)*Q*S*W/(A*T^3) := by
    have heq : (19/200 : ℝ)*(Q*B*S^2)*W/(A*B*S*T^3) =
        (19/200 : ℝ)*Q*S*W/(A*T^3) := by
      field_simp [hAn, hBn, hSn, hTn]
    rw [heq] at hupper
    linarith only [hL, hupper, hfirst]
  have hWlower : alpha*A*T^3/S < W := by
    have hden : 0 < A^2*B^2*(A*T^3) := by positivity
    have h := mul_lt_mul_of_pos_right hwindow hden
    have hclean : A^2*B^2*T^3 <
        (51051/400000 : ℝ)*Q*T^3 + (19/200 : ℝ)*Q*S*W*A*B^2 := by
      field_simp [hAn, hBn, hTn] at h
      nlinarith only [h]
    apply (div_lt_iff₀ hS0).2
    dsimp [alpha]
    apply (mul_lt_mul_iff_of_pos_left (by positivity : 0 < (19/200 : ℝ)*Q*A^2*B^2)).mp
    field_simp [hAn, hBn, hQn]
    nlinarith only [hclean]
  have hT18 : 18 < T := by
    have hprod : (27 : ℝ) ≤ A*B*S := by
      calc
        (27 : ℝ) = 3*3*3 := by norm_num
        _ ≤ A*B*S := by gcongr
    nlinarith only [hprod, hfront]
  have hbase : T^2 ≤ A*T^3/S := by
    apply (le_div_iff₀ hS0).2
    have h1 := mul_le_mul_of_nonneg_left hST (sq_nonneg T)
    have h2 := mul_le_mul_of_nonneg_right (show (1:ℝ)≤A by linarith)
      (le_of_lt (pow_pos hT0 3))
    nlinarith only [h1, h2]
  let Y : ℝ := alpha*A*T^3/S
  change Y < W at hWlower
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hYbase : T^2 < Y := by
    have hmul := mul_lt_mul_of_pos_right halpha (by positivity : 0 < A*T^3/S)
    dsimp [Y]
    exact hbase.trans_lt (by simpa only [one_mul, mul_div_assoc, mul_assoc] using hmul)
  have hT4 : (10000 : ℝ) < T^4 := by
    have ht2 : (324 : ℝ) < T^2 := by nlinarith only [hT18, sq_nonneg (T-18)]
    nlinarith only [ht2, sq_nonneg (T^2-324)]
  have hYsq : (10000 : ℝ) < Y^2 := by
    have hp := mul_pos (sub_pos.mpr hYbase) (by positivity : 0 < Y+T^2)
    nlinarith only [hp, hT4]
  have hWsquare : Y^2 < W^2 := by
    have hp := mul_pos (sub_pos.mpr hWlower) (by positivity : 0 < W+Y)
    nlinarith only [hp]
  have hTC : (9999/10000 : ℝ)*Y^2 < T*C := by
    nlinarith only [hYsq, hWsquare, hroothi]
  apply (mul_lt_mul_iff_of_pos_left hT0).mp
  have heq : T * (((9999/10000 : ℝ)*(200/19)^2) *
      (1/Q-(51051/400000 : ℝ)/(A^2*B^2))^2 * (A^2*T^5/S^2)) =
      (9999/10000 : ℝ)*Y^2 := by
    dsimp [Y, alpha]
    field_simp [hAn, hBn, hSn, hQn]
  rw [heq]
  exact hTC

end D1Bound5
end
