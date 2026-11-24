-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxB.EHc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:46.350793+00:00
-- url     : https://prove2.me/submissions/e3524908-52f4-4e0d-9239-64e74a1a6bb6

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EHc_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.JFxB
theorem _root_.solution (c d : Fin (2 * r + k + 1)) (f : Mat k r → E) : EHc k r 1 c d f = Q.EH k r c d f := by
  rw [EHc_eq, EH_eq]
  simp only [inv_one, one_mul, mul_one]
end Formalism.FourierDecayAlt.P.JFxB
