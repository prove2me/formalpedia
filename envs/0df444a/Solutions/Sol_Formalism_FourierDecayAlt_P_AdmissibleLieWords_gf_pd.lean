-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:01:44.27941+00:00
-- url     : https://prove2.me/submissions/30f257cc-f58c-46b4-adf5-4cdb3aa9f72d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_function_polynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) := by
  exact gram_function_polynomial k r z z'
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
