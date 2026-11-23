-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.MW_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:53.552139+00:00
-- url     : https://prove2.me/submissions/436eb650-5a37-4a26-aa2a-be57c82bf746

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

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
theorem _root_.solution (w : Fin m → K) : (MW w)ᵀ = MW w := by
  ext i j
  simp only [MW, Matrix.transpose_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [hij, Ne.symm hij, if_false]; ring
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
