-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.log_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:32.457342+00:00
-- url     : https://prove2.me/submissions/07e78b38-d4a7-419f-99f4-5fa7a0079d41

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by
  have h3M : (1 : ℝ) ≤ 3 * M := by linarith
  have hL0 : 0 ≤ Real.log (3 * M) := Real.log_nonneg h3M
  have hL : Real.log (3 * M) ≤ (3 * M) ^ ((1 : ℝ) / 4) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (3 * M) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (3 * M) ≤ 2 * Real.sqrt M := by
    rw [← h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log (3 * M) ^ 2 ≤ ((3 * M) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 :=
        pow_le_pow_left₀ hL0 hL 2
    _ = 16 * ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
    _ = 16 * Real.sqrt (3 * M) := by rw [hq]
    _ ≤ 32 * Real.sqrt M := by linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
