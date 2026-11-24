-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.os_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:34:45.643519+00:00
-- url     : https://prove2.me/submissions/0d1d75a6-ea43-40bd-8da6-2633a794aa7d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_t_w0comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mul
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
theorem _root_.solution (x x' : HPar k r') (c : ℂ) (B n n' m : Mat k r') (hn : IsUnit n.det) :
    oneStep k r' x c (n⁻¹ * B * m * n') x' =
      (ιLev k 1 r' n * heis0 k r' x)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * ιLev k 1 r' m *
        (ιLev k 1 r' n' * heis0 k r' x') := by
  have e : w0 k r' c * ιLev k 1 r' n⁻¹ = (ιLev k 1 r' n)⁻¹ * w0 k r' c := by
    rw [t_w0comm k r' c n⁻¹, lev_inv n hn]
  simp only [oneStep, lev_mul, Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (w0 k r' c), e]
  simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.LongWeylElement
