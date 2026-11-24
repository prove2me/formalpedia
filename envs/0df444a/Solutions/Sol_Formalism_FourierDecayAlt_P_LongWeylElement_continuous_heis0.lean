-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.continuous_heis0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:51.532742+00:00
-- url     : https://prove2.me/submissions/bf7de345-74c3-4566-bbbc-6979f79db16a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_continuous_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_continuous_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_continuous_hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_hb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r' : ℕ) : Continuous (heis0 k r') := by
  have hv : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (continuous_lift k r').comp continuous_fst
  have hb' : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := continuous_hb k r'
  have hh : ∀ j, Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) := by
    intro j
    first
      | exact (continuous_herm _).comp (continuous_const.prodMk hv)
      | exact (continuous_herm _).comp (continuous_const.prod_mk hv)
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [heis0, heisG, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hvp : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 p := (continuous_apply p).comp hv
  fun_prop
end Formalism.FourierDecayAlt.P.LongWeylElement
