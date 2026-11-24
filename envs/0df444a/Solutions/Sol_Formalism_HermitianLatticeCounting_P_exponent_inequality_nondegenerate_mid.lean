-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.exponent_inequality_nondegenerate_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:44.862517+00:00
-- url     : https://prove2.me/submissions/1f6be220-8022-4497-bce9-e192f88b9c30

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
    (hl20 : 0 ≤ l2) (hl2 : l2 ≤ L) (hX : 16 * C ^ 32 * (M ^ 5 * F * L) ≤ K) (S lGam : ℝ) (hS2 : 2 ≤ S) (hSK : S ≤ K)
    (hG : lGam ≤ C * M ^ 5 * F * L) :
    ((S - 1) * K * F) * (l2 - lg) + (C * M ^ 2 * F * L * C + S * K * F * lC) + K * F * lC +
      (C * M ^ 2 * F * L) * (C * (S + M) * M ^ 2) + 6 * S * F * (lC + 2 * lk) + lGam ≤
      -(K * F * lg) / 2 - lk := by
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
  have hS0 : 0 ≤ S := by linarith
  have g2 : C ^ 2 * (M ^ 2 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 2 (by norm_num)) (pow_nonneg hC0 2)
  have g5a : C ^ 2 * (M ^ 4 * F * L) ≤ C ^ 2 * (M ^ 5 * F * L) :=
    mul_le_mul_of_nonneg_left (hMY 4 (by norm_num)) (pow_nonneg hC0 2)
  have g5b : S * (C ^ 2 * (M ^ 4 * F * L)) ≤ S * (C ^ 32 * (M ^ 5 * F * L)) :=
    mul_le_mul_of_nonneg_left (g5a.trans hC2Y) hS0
  have g5c : S * (16 * C ^ 32 * (M ^ 5 * F * L)) ≤ S * K := mul_le_mul_of_nonneg_left hX hS0
  have g5d : S * (32 * K) ≤ S * (K * F * lg) := mul_le_mul_of_nonneg_left h32 hS0
  have hSF0 : 0 ≤ S * F := mul_nonneg hS0 hF0
  have g6a : 6 * S * F * (lC + 2 * lk) ≤ 6 * S * F * (3 * lk) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (mul_nonneg (by norm_num) hS0) hF0)
  have g6b : S * F * lk ≤ S * F * (lg / 8) := mul_le_mul_of_nonneg_left hlklg hSF0
  have g6c : 36 * (S * F * lg) ≤ K * (S * F * lg) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hSF0 hlg0)
  have g4 : K * F * lC ≤ K * F * (lg / 256) := mul_le_mul_of_nonneg_left hlClg hKF0
  have hS1K : 0 ≤ (S - 1) * K * F := mul_nonneg (mul_nonneg (by linarith) hK0) hF0
  have g1 : ((S - 1) * K * F) * (l2 - lg) ≤ ((S - 1) * K * F) * (-(7 / 8) * lg) :=
    mul_le_mul_of_nonneg_left (by linarith) hS1K
  have g3 : S * K * F * lC ≤ S * K * F * (lg / 256) :=
    mul_le_mul_of_nonneg_left hlClg (mul_nonneg (mul_nonneg hS0 hK0) hF0)
  have g8a : 1 * (K * F * lg) ≤ (S - 1) * (K * F * lg) := mul_le_mul_of_nonneg_right (by linarith) hW0
  have g8b : 0 ≤ (S - 2) * (K * F * lg) := mul_nonneg (by linarith) hW0
  linarith
end Formalism.HermitianLatticeCounting.P
