-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_left_num
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:42.035511+00:00
-- url     : https://prove2.me/submissions/7ea1ea11-92b7-4e12-b184-1a4449ec3644

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_ge_one

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
theorem _root_.solution (κ G N M T T' σ₁ y : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 20) (hG : 0 ≤ G) (hN0 : 0 ≤ N)
    (hN : N ≤ G * (T * Real.log (M * T) ^ 2)) (hM : 3 ≤ M) (hT : 2 ≤ T) (hT0' : T ≤ T') (hT' : T' ≤ T + 1)
    (hσ : 1 - κ ≤ σ₁) (hσ' : σ₁ ≤ 1 - 3 * κ / 4) (hy : 2 ≤ y) :
    1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hMT : 0 < M * T := mul_pos hM0 hT0
  have hs1 : 19 / 20 ≤ σ₁ := by linarith
  have hs2 : 3 * κ / 4 ≤ 1 - σ₁ := by linarith
  have hs0 : 0 < σ₁ := by linarith
  have hs3 : 0 < 1 - σ₁ := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hsne : σ₁ ≠ 0 := hs0.ne'
  have hs3ne : 1 - σ₁ ≠ 0 := hs3.ne'
  have hs4 : σ₁ ≠ 1 := (by linarith : σ₁ < 1).ne
  have hs5 : (1 : ℝ) ≠ σ₁ := (by linarith : σ₁ < 1).ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hP : 57 * κ / 80 ≤ σ₁ * (1 - σ₁) := by
    nlinarith [mul_le_mul hs1 hs2 (by linarith) hs0.le]
  have hD : 2 * κ ≤ Real.pi * (σ₁ * (1 - σ₁)) := by
    nlinarith [mul_le_mul Real.pi_gt_three.le hP (by linarith) Real.pi_pos.le]
  have hDpos : 0 < Real.pi * (σ₁ * (1 - σ₁)) := by linarith
  have hc0 : 0 ≤ 4 / (3 * κ) := div_nonneg (by norm_num) (by linarith)
  have hL1 : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hLle : Real.log (M * T) ≤ M * T := by
    have := Real.log_le_sub_one_of_pos hMT
    linarith
  have hTL : 1 ≤ T * Real.log (M * T) ^ 2 := by nlinarith
  have hNc : N + 4 / (3 * κ) ≤ (G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hTL hc0]
  have hT'le : T' ≤ 3 * T / 2 := by linarith
  have hnum1 : T' * (N + 4 / (3 * κ)) ≤
      (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) :=
    mul_le_mul hT'le hNc (by linarith) (by linarith)
  have hGc : 0 ≤ G + 4 / (3 * κ) := by linarith
  have hTMT : T ≤ M * T := by nlinarith
  have hTL2 : T * Real.log (M * T) ≤ (M * T) * (M * T) :=
    mul_le_mul hTMT hLle (by linarith) hMT.le
  have hQ : (T * Real.log (M * T)) * (T * Real.log (M * T)) ≤
      ((M * T) * (M * T)) * ((M * T) * (M * T)) :=
    mul_le_mul hTL2 hTL2 (mul_nonneg hT0.le (by linarith)) (mul_self_nonneg _)
  have hnum2 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) ≤
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hGc
    have h2 := mul_nonneg hGc (pow_nonneg hMT.le 4)
    have e1 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) =
        3 / 2 * ((G + 4 / (3 * κ)) * ((T * Real.log (M * T)) * (T * Real.log (M * T)))) := by ring
    have e2 : (G + 4 / (3 * κ)) * (((M * T) * (M * T)) * ((M * T) * (M * T))) =
        (G + 4 / (3 * κ)) * (M * T) ^ 4 := by ring
    rw [e1]
    rw [e2] at h1
    linarith
  have hk0 : 0 ≤ 2 / κ := div_nonneg (by norm_num) hκ.le
  have hB0 : 0 ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGc) hk0) (pow_nonneg hMT.le 4)
  have hB2 : 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) =
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    field_simp
    ring
  have hchain : T' * (N + 4 / (3 * κ)) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
    calc T' * (N + 4 / (3 * κ)) ≤ 12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := hnum1.trans hnum2
      _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) := hB2.symm
      _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
          mul_le_mul_of_nonneg_left hD hB0
  have hA : T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 := by
    rw [div_le_iff₀ hDpos]; exact hchain
  have hA0 : 0 ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hDpos.le
  have hYle : y ^ σ₁ / y ≤ y ^ (-(κ / 2)) := by
    rw [← Real.rpow_sub_one hyne]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 ≤ y ^ (-(κ / 2)) := Real.rpow_nonneg hy0.le _
  calc 1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)))
        = T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * (y ^ σ₁ / y) := by
        field_simp
    _ ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_left hYle hA0
    _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_right hA hY0
    _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
