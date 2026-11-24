-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.xi_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:51.355966+00:00
-- url     : https://prove2.me/submissions/ef0bda6a-8139-4e7c-95cd-554001d07b70

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_liftVec_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_first_ne_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_liftVec_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_dual_base_vector_eq_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_e0_eq


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
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (p : ℂ × HPar k r') : xi k r' p (iL k r') = p.1 := by
  simp [xi, dual_base_vector_eq_single, e0_eq, liftVec_last, Pi.single_apply, (first_ne_last (k := k) (r' := r')).symm]
end Formalism.FourierDecayAlt.P.B2x9
