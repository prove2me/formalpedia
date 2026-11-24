-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.tau_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:18.031411+00:00
-- url     : https://prove2.me/submissions/175049da-c774-4ba6-8d39-819ab28584dc

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_tau_eq_oneStep

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
theorem _root_.solution (hG : ClosedG) (HI : HeisInv) (OM : OneStepMem) (p : ℂ × HPar k r') (hc : p.1 ≠ 0) :
    (Matrix.of (tau k r' p) : Mat k (1 + r')) ∈ GV k (1 + r') := by
  have h1 : (1 : Mat k r') ∈ GV k r' := by
    first
      | exact (hG k r').one_mem
      | exact (hG k r').2.1
      | exact (hG k r').1.1
      | exact (hG k r').one
      | exact (hG k r').2.2.1
  rw [tau_eq_oneStep HI p]
  exact (OM k r' (-p.2.1, -p.2.2) (0, 0) p.1 hc 1 h1).1
end Formalism.FourierDecayAlt.P.B2x9
