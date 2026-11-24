-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exponent_inequality_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:45.109577+00:00
-- url     : https://prove2.me/submissions/93887385-20dc-471f-a828-283cde645b41

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (C K F M L lk lg lC l2 : ℝ) (hC : 1 ≤ C) (h4M : 4 ≤ M) (hMF : M ≤ F) (hFK : F ≤ K)
    (hL : 0.69 ≤ L) (hlk : 1 ≤ lk) (hlC0 : 0 ≤ lC) (hlC : 32 * lC ≤ lk) (hlg : 8 * (lk + L) ≤ lg)
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (R lGam : ℝ) (hR : 1 ≤ R) (hMR : M = 2 * R + 2)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    F * lC + (C * M ^ 2 * F * L) * (C * M ^ 3) + lGam + C * M ^ 6 * F * L +
      (K * F) * (lC - (2 * R + 1) * lg - R * lk) / 2 ≤ -(K * F * lk) := by
  have hM0 : 0 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hlk0 : 0 ≤ lk := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC32 : C ≤ C ^ 32 := le_self_pow₀ hC (by norm_num)
  have hC2 : C ^ 2 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hC3 : C ^ 3 ≤ C ^ 32 := pow_le_pow_right₀ hC (by norm_num)
  have hY0 : 0 ≤ M ^ 5 * F * L := mul_nonneg (mul_nonneg (pow_nonneg hM0 5) hF0) hL0
  have hZ0 : 0 ≤ C ^ 32 * (M ^ 5 * F * L) := mul_nonneg (pow_nonneg hC0 32) hY0
  have hM5 : 1024 ≤ M ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h4M 5
    norm_num at h
    linarith
  have hF4 : 4 ≤ F := by linarith
  have hM5F : 1024 * 4 ≤ M ^ 5 * F := mul_le_mul hM5 hF4 (by norm_num) (by linarith)
  have hY : 1024 * 4 * 0.69 ≤ M ^ 5 * F * L := mul_le_mul hM5F hL (by norm_num) (by linarith)
  have hYC : M ^ 5 * F * L ≤ C ^ 32 * (M ^ 5 * F * L) := le_mul_of_one_le_left hY0 (one_le_pow₀ hC)
  have hC1Y : C * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC32 hY0
  have hC2Y : C ^ 2 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC2 hY0
  have hC3Y : C ^ 3 * (M ^ 5 * F * L) ≤ C ^ 32 * (M ^ 5 * F * L) := mul_le_mul_of_nonneg_right hC3 hY0
  have hKbig : 40000 ≤ K := by linarith
  have hFlk : 4 * 1 ≤ F * lk := mul_le_mul hF4 hlk (by norm_num) hF0
  have hKP : K * (4 * 1) ≤ K * (F * lk) := mul_le_mul_of_nonneg_left hFlk hK0
  have hKF0 : 0 ≤ K * F := mul_nonneg hK0 hF0
  have hKF1000 : 40000 * 4 ≤ K * F := mul_le_mul hKbig hF4 (by norm_num) hK0
  have hFKP : K * F * 1 ≤ K * F * lk := mul_le_mul_of_nonneg_left hlk hKF0
  have hPlk : (40000 * 4) * lk ≤ K * F * lk := mul_le_mul_of_nonneg_right hKF1000 hlk0
  have hlg8 : 8 ≤ lg := by linarith
  have hFlg : 4 * 8 ≤ F * lg := mul_le_mul hF4 hlg8 (by norm_num) hF0
  have h32' : K * (4 * 8) ≤ K * (F * lg) := mul_le_mul_of_nonneg_left hFlg hK0
  have h32 : 32 * K ≤ K * F * lg := by linarith
  have hW0 : 0 ≤ K * F * lg := mul_nonneg hKF0 hlg0
  have hlgW : 1 * lg ≤ K * F * lg := mul_le_mul_of_nonneg_right (by linarith) hlg0
  have hMY : ∀ j : ℕ, j ≤ 5 → M ^ j * F * L ≤ M ^ 5 * F * L := fun j hj =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 hj) hF0) hL0
  have hM1Y : M * F * L ≤ M ^ 5 * F * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_self_pow₀ hM1 (by norm_num)) hF0) hL0
  have hlClk : lC ≤ lk / 32 := by linarith
  have hlklg : lk ≤ lg / 8 := by linarith
  have hLlg : L ≤ lg / 8 := by linarith
  have hlClg : lC ≤ lg / 256 := by linarith
  have hG1 : lGam ≤ C * (M ^ 5 * F * L) := by linarith
  have f1 : F * lC ≤ F * (lk / 32) := mul_le_mul_of_nonneg_left hlClk hF0
  have f1b : 1 * (F * lk) ≤ K * (F * lk) :=
    mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ K) (mul_nonneg hF0 hlk0)
  have f4a : M * (C * (M ^ 5 * F * L)) ≤ M * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_left hC1Y hM0
  have f4b : M * (C ^ 32 * (M ^ 5 * F * L)) ≤ F * (C ^ 32 * (M ^ 5 * F * L)) := mul_le_mul_of_nonneg_right hMF hZ0
  have f4c : F * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ F * K := mul_le_mul_of_nonneg_left hX hF0
  have hR1 : 0 ≤ (R - 1) * lg := mul_nonneg (by linarith) hlg0
  have hR2 : 0 ≤ (R - 1) * lk := mul_nonneg (by linarith) hlk0
  have hD : lC - (2 * R + 1) * lg - R * lk ≤ -23 * lk := by linarith
  have f5 : K * F * (lC - (2 * R + 1) * lg - R * lk) ≤ K * F * (-23 * lk) := mul_le_mul_of_nonneg_left hD hKF0
  linarith
end Formalism.HermitianLatticeCounting.P
