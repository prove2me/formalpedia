-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dmin_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:57.651701+00:00
-- url     : https://prove2.me/submissions/b2e22866-886a-41ff-81c3-60ec93112abf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Theorems.Thm_Formalism_FourierDecayAlt_P_minor_polynomial_property


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
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg (2 * r + 2) (fun g : Mat k r => Dmin k r z z' g l) := by
  obtain ⟨q, hq, he⟩ := minor_polynomial_property k r z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), he⟩
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
