-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rootsFinite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:27.794104+00:00
-- url     : https://prove2.me/submissions/566afc7c-1803-46e7-97a9-ec40a7fd3cb9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_roots_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.RootsFinite := by
  intro K _ _ _ s hs D
  refine ((roots_finite s hs (D : K)).preimage (Units.val_injective.injOn)).subset ?_
  intro z hz
  have hz' : z ^ s = D := hz
  change (z : K) ^ s = (D : K)
  rw [← hz', Units.val_pow_eq_pow_val]
end Formalism.FourierDecayAlt.P
