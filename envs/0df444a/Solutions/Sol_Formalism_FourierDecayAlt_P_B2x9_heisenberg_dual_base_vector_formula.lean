-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.heisenberg_dual_base_vector_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:51.74882+00:00
-- url     : https://prove2.me/submissions/56c22111-aaeb-4735-ae67-7871d5cb774f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_e0_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_hermitian_dual_base_vector_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_liftVec_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq
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
theorem _root_.solution (HA : HeisAct) (x : HPar k r') :
    heis0 k r' x *ᵥ es0 k r' = es0 k r' + liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r' := by
  unfold heis0
  rw [HA k r', hermitian_dual_base_vector_left, hermitian_dual_base_vector_left, liftVec_first]
  have he : e0 k r' (iF k r') = 1 := by rw [e0_eq]; exact Pi.single_eq_same _ _
  rw [he]
  simp only [star_zero, zero_smul, sub_zero, star_one, one_smul]
  abel
end Formalism.FourierDecayAlt.P.B2x9
