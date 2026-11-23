-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.mulLeft_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:41.259554+00:00
-- url     : https://prove2.me/submissions/d854edf0-ea18-4a83-a266-270d9007ed67

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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (b : Kˣ) : Function.Injective (AddMonoidHom.mulLeft (b : K)) := by
  intro x y hxy
  exact b.isUnit.mul_left_cancel hxy
end Formalism.FourierDecayAlt.P.A6x3
