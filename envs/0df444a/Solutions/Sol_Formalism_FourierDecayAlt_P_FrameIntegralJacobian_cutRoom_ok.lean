-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.cutRoom_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:47.604123+00:00
-- url     : https://prove2.me/submissions/84dd1d63-b6b4-4aab-a82c-8994e2710050

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
theorem _root_.solution : CutRoom := by
  unfold CutRoom
  intro r α β h
  refine ⟨by ring, fun k hk => ⟨?_, ?_⟩⟩
  · have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · have hk' : ((k:ℝ) + 1) ≤ 6 * ((r:ℝ) + 1) ^ 2 := by
      exact_mod_cast (show k + 1 ≤ 6 * (r + 1) ^ 2 from hk)
    linarith
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
