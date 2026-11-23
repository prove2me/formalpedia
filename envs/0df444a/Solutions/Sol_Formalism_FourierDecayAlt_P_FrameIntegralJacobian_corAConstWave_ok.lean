-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.corAConstWave_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:47.162349+00:00
-- url     : https://prove2.me/submissions/fb159304-f992-40b2-a870-f7de19407fe5

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : CorAConstWave := by
  unfold CorAConstWave
  refine ⟨fun n ell Qw BBs BB hell hn hQ0 hQ hB0 hB => ?_, fun Qw BBs BB hQ0 hQ hB0 hB => ?_⟩
  · have h2 : Real.exp (1 / 2) = Real.exp (1 / 4) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp (1 / 4) := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp (1 / 4) ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp (1 / 4) := Real.sqrt_sq (Real.exp_pos _).le
    have h4 : 0 ≤ 4 / ell := div_nonneg (by norm_num) hell.le
    have hP : 0 ≤ (1 / 2 : ℝ) * (4 / ell) ^ n := mul_nonneg (by norm_num) (pow_nonneg h4 n)
    have hm : Real.sqrt Qw * BBs ≤ Real.exp (1 / 4) * BB :=
      mul_le_mul hs hB hB0 (Real.exp_pos _).le
    calc (1 / 2) * (4 / ell) ^ n * Real.sqrt Qw * BBs
        = ((1 / 2) * (4 / ell) ^ n) * (Real.sqrt Qw * BBs) := by ring
      _ ≤ ((1 / 2) * (4 / ell) ^ n) * (Real.exp (1 / 4) * BB) := mul_le_mul_of_nonneg_left hm hP
      _ = Real.exp (1 / 4) * (1 / 2) * (4 / ell) ^ n * BB := by ring
  · have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hs : Real.sqrt Qw ≤ Real.exp 1 := by
      calc Real.sqrt Qw ≤ Real.sqrt (Real.exp 1 ^ 2) := Real.sqrt_le_sqrt (by rw [← h2]; exact hQ)
        _ = Real.exp 1 := Real.sqrt_sq (Real.exp_pos _).le
    exact mul_le_mul hs hB hB0 (Real.exp_pos _).le
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
