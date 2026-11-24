-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.swap4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:36:36.457299+00:00
-- url     : https://prove2.me/submissions/6807d4df-2ec6-4db7-a955-db7837ba44ec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
variable {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (μ₁ : Measure α) (ν₁ : Measure β) (μ₂ : Measure α') (ν₂ : Measure β') [SFinite μ₁] [SFinite ν₁]
    [SFinite μ₂] [SFinite ν₂] (F : (α × β) × (α' × β') → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ u, F u ∂((μ₁.prod ν₁).prod (μ₂.prod ν₂)) =
      ∫⁻ p : (α × α') × (β × β'), F ((p.1.1, p.2.1), (p.1.2, p.2.2)) ∂((μ₁.prod μ₂).prod (ν₁.prod ν₂)) := by
  have m1 : Measurable fun p : (α × α') × (β × β') => F ((p.1.1, p.2.1), (p.1.2, p.2.2)) :=
    hF.comp (by fun_prop)
  have e1 : ∀ x : α × β, ∫⁻ y, F (x, y) ∂(μ₂.prod ν₂) = ∫⁻ a', ∫⁻ b', F (x, (a', b')) ∂ν₂ ∂μ₂ := by
    intro x
    exact lintegral_prod (fun y : α' × β' => F (x, y)) (hF.comp (by fun_prop)).aemeasurable
  have e2 : ∀ x : α × α', ∫⁻ y, F ((x.1, y.1), (x.2, y.2)) ∂(ν₁.prod ν₂) =
      ∫⁻ b, ∫⁻ b', F ((x.1, b), (x.2, b')) ∂ν₂ ∂ν₁ := by
    intro x
    exact lintegral_prod (fun y : β × β' => F ((x.1, y.1), (x.2, y.2))) (hF.comp (by fun_prop)).aemeasurable
  have m2 : Measurable fun x : α × β => ∫⁻ a', ∫⁻ b', F (x, (a', b')) ∂ν₂ ∂μ₂ :=
    ((hF.comp (by fun_prop : Measurable fun q : ((α × β) × α') × β' => (q.1.1, (q.1.2, q.2)))).lintegral_prod_right').lintegral_prod_right'
  have m3 : Measurable fun x : α × α' => ∫⁻ b, ∫⁻ b', F ((x.1, b), (x.2, b')) ∂ν₂ ∂ν₁ :=
    ((hF.comp (by fun_prop : Measurable fun q : ((α × α') × β) × β' => ((q.1.1.1, q.1.2), (q.1.1.2, q.2)))).lintegral_prod_right').lintegral_prod_right'
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ m1.aemeasurable]
  try dsimp only
  simp_rw [e1, e2]
  rw [lintegral_prod _ m2.aemeasurable, lintegral_prod _ m3.aemeasurable]
  try dsimp only
  refine lintegral_congr fun a => ?_
  have m4 : Measurable (Function.uncurry fun (b : β) (a' : α') => ∫⁻ b', F ((a, b), (a', b')) ∂ν₂) :=
    (hF.comp (by fun_prop : Measurable fun q : (β × α') × β' => ((a, q.1.1), (q.1.2, q.2)))).lintegral_prod_right'
  exact lintegral_lintegral_swap m4.aemeasurable
end Formalism.FourierDecayAlt.P.LongWeylElement
