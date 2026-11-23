-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.addChar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:59.423391+00:00
-- url     : https://prove2.me/submissions/0597e046-0243-4411-9e2b-8cf599999020

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
theorem _root_.solution {G : Type} [AddGroup G] (φ : AddChar G ℂ) (x : G) : φ x ≠ 0 := by
  intro h
  have := φ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this
end Formalism.FourierDecayAlt.P.A6x4
