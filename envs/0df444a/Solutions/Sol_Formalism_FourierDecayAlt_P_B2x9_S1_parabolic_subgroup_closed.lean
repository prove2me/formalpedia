-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.parabolic_subgroup_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:48.379844+00:00
-- url     : https://prove2.me/submissions/61dce473-d379-4aab-b33a-6f64f6a6ec4c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9 Formalism.FourierDecayAlt.P.B2x9.S1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9.S1
theorem _root_.solution (hG : ClosedG) : IsClosed (P1set k r') := by
  have hc : IsClosed {g : Mat k (1 + r') | g *ᵥ e0 k r' = e0 k r'} :=
    isClosed_eq (by first | exact continuous_id.matrix_mulVec continuous_const | fun_prop | continuity)
      continuous_const
  have hG' := hG k (1 + r')
  first
    | exact hG'.1.inter hc
    | exact hG'.isClosed.inter hc
    | exact hG'.closed.inter hc
    | exact hG'.2.inter hc
end Formalism.FourierDecayAlt.P.B2x9.S1
