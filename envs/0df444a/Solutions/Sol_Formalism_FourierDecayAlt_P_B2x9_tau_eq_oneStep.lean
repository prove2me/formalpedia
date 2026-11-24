-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.tau_eq_oneStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:46.36545+00:00
-- url     : https://prove2.me/submissions/6b9e0f8c-1dd1-444c-9822-3fc69d70a039

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heis_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (HI : HeisInv) (p : ℂ × HPar k r') :
    (Matrix.of (tau k r' p) : Mat k (1 + r')) = oneStep k r' (-p.2.1, -p.2.2) p.1 1 (0, 0) := by
  change heis0 k r' p.2 * w0 k r' p.1 = oneStep k r' (-p.2.1, -p.2.2) p.1 1 (0, 0)
  unfold oneStep
  rw [HI k r', lev_one, heis_zero]
  simp
end Formalism.FourierDecayAlt.P.B2x9
