-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.lint_lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:09:34.151188+00:00
-- url     : https://prove2.me/submissions/25d701b9-0eb6-4b9f-99b8-ee52fc85be2b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GNSandwich
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
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


section
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
private theorem lintegral_comp_eq_of_map_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}
    (hμ : μ.map f = μ) {G : α → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (f x) ∂μ = ∫⁻ x, G x ∂μ := by
  by_cases hf : AEMeasurable f μ
  · conv_rhs => rw [← hμ]
    rw [lintegral_map' hG.aemeasurable hf]
  · have h0 : μ = 0 := by
      rw [← hμ]
      exact Measure.map_of_not_aemeasurable hf
    simp [h0]
end Formalism.FourierDecayAlt.P.S3dx4
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} {a : Mx k r} (hμ : μ.map (Formalism.QuantumDeterminants.lmulM a) = μ)
    {G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (Formalism.QuantumDeterminants.lmulM a x) ∂μ = ∫⁻ x, G x ∂μ := by
  exact lintegral_comp_eq_of_map_eq hμ hG
end Formalism.FourierDecayAlt.P.S3dx4
