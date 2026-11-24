-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.hb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:07:10.062887+00:00
-- url     : https://prove2.me/submissions/51e9929e-5117-43c0-9170-d050880e13b3

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_herm_cont

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
theorem _root_.solution : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 :=
    (herm_cont (Hpk k r')).comp (by fun_prop : Continuous fun x : HPar k r' => (x.1, x.1))
  unfold hb
  exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp h1).neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
end Formalism.FourierDecayAlt.P.B2x9
