-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.S1.heis_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:11.947456+00:00
-- url     : https://prove2.me/submissions/38fcf5c5-71af-4554-8ff7-22036693f834

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_base_vector_levi_coordinate_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_hermitian_levi_vector_base_orthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_S1_levPos_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levPos_inj


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
theorem _root_.solution (x : HPar k r') (i j : Fin (2 * r' + k + 1)) :
    heis0 k r' x (levPos k 1 r' i) (levPos k 1 r' j) = if i = j then 1 else 0 := by
  simp only [heis0, heisG, Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, base_vector_levi_coordinate_zero,
    hermitian_levi_vector_base_orthogonal, zero_mul, mul_zero, sub_zero, add_zero, Matrix.one_apply, levPos_inj.eq_iff]
end Formalism.FourierDecayAlt.P.B2x9.S1
