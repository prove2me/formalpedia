-- Prove2me | solution 1 for Formalism.L2.Th1.H.quadraticSemicharacters_of_productThetaMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:53.88674+00:00
-- url     : https://prove2.me/submissions/3352be8f-455a-4df8-a79e-c759a375d82d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_QuadraticSemicharactersOfProductThetaMem
import Theorems.Thm_Formalism_L2_Th1_H_InterReps_of
import Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_const_mul
import Theorems.Thm_Formalism_L2_Th1_H_Inv_opU_finset_sum
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergFourfold
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergIsometry
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergMul
import Theorems.Thm_Formalism_L2_Th1_H_heisenbergStandard
import Theorems.Thm_Formalism_L2_Th1_H_semicharacterHom
import Theorems.Thm_Formalism_L2_Th1_H_standardFormBasic


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (hF0 : ProductThetaMem) : quadraticSemicharacterIdentityReformulated₂ := by
  intro L ω₀ n _ _ h Λ α β g D ε θ hθ S hS t y
  have hH : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hfix : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) :=
    ((hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd).1).2

  have h1 : tens4 (opU (matH h) t θ) (g.symm y)
      = opU (matH (blk4 h)) (fun w => t w.2) (tens4 θ) (g.symm y) :=
    ((heisenbergFourfold n h).2 (fun w => t w.2) (fun _ => θ) (g.symm y)).symm

  have h2 : tens4 θ = fun v => ε * (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z)
          ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) v) := by
    rw [hθ]
    funext v
    have := InterReps_of semicharacterHom (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hH (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi _ hfix S hS (g v)
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [this]
    rfl
  rw [h1, h2, Inv.opU_const_mul]
  erw [heisenbergIsometry _ _ _ _ _ D.isom (fun w => t w.2) (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z) (g.symm y)]
  rw [Inv.opU_const_mul, Inv.opU_finset_sum]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Inv.opU_const_mul, heisenbergMul _ _ hH, F0, heisenbergStandard]
  simp only [Pi.add_apply]
  ring
end Formalism.L2.Th1.H
