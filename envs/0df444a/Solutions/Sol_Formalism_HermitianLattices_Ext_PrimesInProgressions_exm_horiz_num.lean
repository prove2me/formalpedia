-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_horiz_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:55.122971+00:00
-- url     : https://prove2.me/submissions/bdbb07c1-eeec-4e9d-b8f7-31d2ba52b090

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_y

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (G N T T' y l : ℝ) (hG : 0 ≤ G) (hN0 : 0 ≤ N) (hN : N ≤ G * (T * l ^ 2))
    (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) ≤
      3 * (G + 1) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have key : 1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) =
      3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) := by
    field_simp
  have hX : 0 ≤ Real.exp 1 / (2 * Real.pi * T' ^ 2) := by positivity
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hTl : 1 ≤ T * l ^ 2 := by nlinarith
  have hN1 : 3 * (N + 1) ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  have hA : Real.exp 1 ≤ 2 * Real.pi * Real.log y := by
    nlinarith [Real.exp_one_lt_d9, Real.pi_gt_three, mul_le_mul_of_nonneg_left hLy Real.pi_pos.le]
  have hTT : T ^ 2 ≤ T' ^ 2 := by nlinarith
  have hprod : Real.exp 1 * T ^ 2 ≤ Real.log y * (2 * Real.pi * T' ^ 2) := by
    nlinarith [mul_le_mul hA hTT (sq_nonneg T) (by nlinarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi * Real.log y)]
  have h1 : Real.exp 1 / (2 * Real.pi * T' ^ 2) ≤ Real.log y / T ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos two_pos Real.pi_pos) (pow_pos hT'0 2)) (pow_pos hT0 2)]; exact hprod
  have hB : 0 ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  rw [key]
  calc 3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2))
        ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) :=
        mul_le_mul_of_nonneg_right hN1 hX
    _ ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.log y / T ^ 2) := mul_le_mul_of_nonneg_left h1 hB
    _ = 3 * (G + 1) * (Real.log y * l ^ 2 / T) := by field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
