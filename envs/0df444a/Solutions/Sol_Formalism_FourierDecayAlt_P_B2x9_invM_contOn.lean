-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.invM_contOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:28.632855+00:00
-- url     : https://prove2.me/submissions/695d27e0-94bb-42c5-a557-b5065de2a61d

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
theorem _root_.solution : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn
end Formalism.FourierDecayAlt.P.B2x9
