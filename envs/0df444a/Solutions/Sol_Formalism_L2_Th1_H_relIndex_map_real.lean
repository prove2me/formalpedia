-- Prove2me | solution 1 for Formalism.L2.Th1.H.relIndex_map_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:45.833322+00:00
-- url     : https://prove2.me/submissions/182e7de3-3959-4fb9-a68c-c5d610b8cba8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
import Theorems.Thm_Formalism_L2_Th1_H_relIndex_eq_abs_det_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L₁ L₂ : AddSubgroup E) (h : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℝ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂))
    (f : E ≃ₗ[ℝ] E) (hf : L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom ≤ L₂) :
    ((L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom).relIndex L₂ : ℝ)
      = (L₁.relIndex L₂ : ℝ) * |LinearMap.det (f : E →ₗ[ℝ] E)| := by
  classical
  have hb : L₁.map (f : E →ₗ[ℝ] E).toAddMonoidHom = .closure (Set.range (b₁.map f)) := by
    rw [h₁, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 1
  rw [relIndex_eq_abs_det_real _ L₂ hf (b₁.map f) b₂ hb h₂,
    relIndex_eq_abs_det_real L₁ L₂ h b₁ b₂ h₁ h₂]
  have e : ⇑(b₁.map f) = (f : E →ₗ[ℝ] E) ∘ b₁ := by ext i; simp
  rw [e, Basis.det_comp, abs_mul, mul_comm]
end Formalism.L2.Th1.H
