-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.charOf_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:20.155922+00:00
-- url     : https://prove2.me/submissions/e2d97dd2-194d-4ed6-9130-6aa99868d739

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (A : AddSubgroup K) {L : AddSubgroup K} {z : K} (hz : z ∈ perp ψ L) (r : A) :
    charOf A hz (r : A ⧸ L.addSubgroupOf A) = ψ (z * (r : K)) := psi_out hz r
end Formalism.FourierDecayAlt.P.A6x3
