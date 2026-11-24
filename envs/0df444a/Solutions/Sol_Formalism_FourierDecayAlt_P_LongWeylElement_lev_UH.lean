-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:16.510456+00:00
-- url     : https://prove2.me/submissions/2736a2a3-8d30-4638-95ad-66e844e1fa43

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_t_w0comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_Hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_long_weyl_element_sq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mul
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (g : Mat k r') : ιLev k 1 r' g ∈ GV k (1 + r') ↔ g ∈ GV k r' := by
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r') ↔ gᴴ * Hpk k r' * g = Hpk k r'
  have key : (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = w0 k r' 1 * ιLev k 1 r' (gᴴ * Hpk k r' * g) := by
    rw [lev_conjT, Hpk_eq, ← Matrix.mul_assoc, ← t_w0comm k r' 1 gᴴ]
    simp only [Matrix.mul_assoc, ← lev_mul]
  rw [key, Hpk_eq]
  constructor
  · intro h
    apply lev_inj
    have := congrArg (fun M => w0 k r' 1 * M) h
    simpa only [← Matrix.mul_assoc, long_weyl_element_sq_one, Matrix.one_mul] using this
  · intro h
    rw [h]
end Formalism.FourierDecayAlt.P.LongWeylElement
