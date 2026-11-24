-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.tau_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:37.120533+00:00
-- url     : https://prove2.me/submissions/7c9239aa-b478-4d9c-91dc-bc8099012f65

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_heisenberg_map_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_long_weyl_family_measurable

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
theorem _root_.solution : Measurable (tau k r') := by
  have h1 : Measurable fun p : ℂ × HPar k r' => heisF k r' p.2 := heisenberg_map_continuous.measurable.comp measurable_snd
  have h2 : Measurable fun p : ℂ × HPar k r' => w0F k r' p.1 := long_weyl_family_measurable.comp measurable_fst
  unfold tau
  apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum; intro l _
  exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp h1)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply l).comp h2))
end Formalism.FourierDecayAlt.P.B2x9
