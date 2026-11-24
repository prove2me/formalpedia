-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.invM_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:20.635155+00:00
-- url     : https://prove2.me/submissions/12e6bbd7-50bf-4060-8635-7f4d7e73cfb5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_detF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_adjF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_invM_smul

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
theorem _root_.solution : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  first
    | exact (detF_cont.measurable.inv).smul adjF_cont.measurable
    | (apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
       exact (detF_cont.measurable.inv).mul (((continuous_apply j).comp ((continuous_apply i).comp adjF_cont)).measurable))
end Formalism.FourierDecayAlt.P.B2x9
