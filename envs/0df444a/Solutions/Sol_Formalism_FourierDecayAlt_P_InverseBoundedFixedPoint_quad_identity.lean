-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:14.1938+00:00
-- url     : https://prove2.me/submissions/53e0379a-9164-4732-a245-ee9aac408e40

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_quad_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_phase_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) :
    y ⬝ᵥ (MW w *ᵥ y) = 2 * (∑ k, y k + ∏ k, w k - 1) := by
  rw [quad_expand, phase_identity y w h]
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
