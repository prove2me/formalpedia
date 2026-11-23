-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.realFrameEntry_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:51.13135+00:00
-- url     : https://prove2.me/submissions/495e5159-ecd7-4c9b-b2f8-061c2b88b3b5

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
theorem _root_.solution : RealFrameEntry := by
  unfold RealFrameEntry
  intro rd r a b i s hrd
  refine ⟨?_, fun h => by omega⟩
  rw [← zpow_add₀ hrd.ne']
  congr 1
  ring
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
