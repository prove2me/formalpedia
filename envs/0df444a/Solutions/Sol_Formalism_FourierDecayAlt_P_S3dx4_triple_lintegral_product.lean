-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.triple_lintegral_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:29.673112+00:00
-- url     : https://prove2.me/submissions/3aa54c3b-b619-4b23-b68c-870d06f06724

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleIntegrandMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_mt_cont
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
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {e1 e2 : Mx k r → ℂ} (he1 : Continuous e1) (he2 : Continuous e2) (γi : Mx k r)
    (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x : Formalism.QuantumDeterminants.Mt k r) :
    (∫⁻ p, ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ ∂μp) *
      (∫⁻ q, ‖e2 (Matrix.of q.1 * Matrix.of q.2 * (γi * Matrix.of x))‖ₑ ∂μq) =
      ∫⁻ p, ∫⁻ q, Phi3 e1 e2 γi x p q ∂μq ∂μp := by
  simp only [Phi3]
  have ha : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ₑ :=
    (he1.comp (((mt_cont.comp continuous_fst).matrix_mul (mt_cont.comp continuous_snd)).matrix_mul
      continuous_const)).enorm.measurable
  rw [← lintegral_mul_const _ ha]
  refine lintegral_congr fun p => ?_
  rw [lintegral_const_mul' _ _ enorm_ne_top]
end Formalism.FourierDecayAlt.P.S3dx4
