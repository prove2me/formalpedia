-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightedKernelPSD_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.89749+00:00
-- url     : https://prove2.me/submissions/ecd840b3-f05f-4bf5-a54b-39f0c25438a5

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
theorem _root_.solution : WeightedKernelPSD := by
  unfold WeightedKernelPSD
  intro H _ Kn n hK hn
  classical
  have hst : ∀ h : H, star (((Real.sqrt (n h) : ℝ)) : ℂ) = ((Real.sqrt (n h) : ℝ) : ℂ) :=
    fun h => Complex.conj_ofReal _
  have hB := hK.conjTranspose_mul_mul_same (Matrix.diagonal fun h => ((Real.sqrt (n h) : ℝ) : ℂ))
  convert hB using 1
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Pi.star_apply,
    hst, Matrix.of_apply, Complex.ofReal_mul]
  try ring
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
