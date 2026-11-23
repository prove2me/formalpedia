-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.sympl_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:55.185381+00:00
-- url     : https://prove2.me/submissions/df72011c-98af-43df-acb8-8d3e67a050d2

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Theorems.Thm_CompanionTheory_ThKR_LL_exp_mul_exp_neg
import Theorems.Thm_CompanionTheory_ThKF_E_sympl_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (NormedSpace.exp X *ᵥ w) (NormedSpace.exp X *ᵥ w') = sympl w w' := by
  have h : Xᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -X :=
    (mem_skewAdjointMatricesSubmodule _ _).1 ((mem_skewAdjointMatricesLieSubalgebra _ _).1 hX)
  have hu : IsUnit (Matrix.J l ℝ) :=
    ⟨⟨Matrix.J l ℝ, -Matrix.J l ℝ, by rw [mul_neg, J_squared, neg_neg], by rw [neg_mul, J_squared, neg_neg]⟩, rfl⟩
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h1 : Xᵀ = Matrix.J l ℝ * -X * (Matrix.J l ℝ)⁻¹ := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᵀ * (Matrix.J l ℝ * NormedSpace.exp X) = Matrix.J l ℝ := by
    have := exp_mul_exp_neg (-X)
    rw [neg_neg] at this
    rw [← Matrix.exp_transpose, h1, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Matrix.J l ℝ),
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul, Matrix.mul_assoc, this, Matrix.mul_one]
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]
end CompanionTheory.ThKR.LL
