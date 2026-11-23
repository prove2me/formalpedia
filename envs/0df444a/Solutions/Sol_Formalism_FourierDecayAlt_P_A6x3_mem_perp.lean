-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.mem_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:59.048971+00:00
-- url     : https://prove2.me/submissions/9194e5c7-1f6b-4ab9-a853-edae920153c2

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
theorem _root_.solution {L : AddSubgroup K} {a : K} : a ∈ perp ψ L ↔ ∀ l ∈ L, ψ (a * l) = 1 := Iff.rfl
end Formalism.FourierDecayAlt.P.A6x3
