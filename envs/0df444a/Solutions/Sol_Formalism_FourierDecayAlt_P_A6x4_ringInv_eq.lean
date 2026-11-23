-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.ringInv_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.548056+00:00
-- url     : https://prove2.me/submissions/40e88e62-f0ac-4886-9532-c8d6cfb9f950

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {z a : K} (h : z * a = 1) : Ring.inverse z = a := by
  have hz : IsUnit z := IsUnit.of_mul_eq_one a h
  calc Ring.inverse z = Ring.inverse z * (z * a) := by rw [h, mul_one]
    _ = (Ring.inverse z * z) * a := by ring
    _ = a := by rw [Ring.inverse_mul_cancel z hz, one_mul]
end Formalism.FourierDecayAlt.P.A6x4
