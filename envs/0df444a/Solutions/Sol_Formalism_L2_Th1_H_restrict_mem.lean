-- Prove2me | solution 1 for Formalism.L2.Th1.H.restrict_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:36.353488+00:00
-- url     : https://prove2.me/submissions/d4379c82-3721-4511-83b4-28c2fde470d5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_slice_add
import Theorems.Thm_Formalism_L2_Th1_H_blockSlice_firstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_firstBlockEmb_mem_fourfoldLattice
import Theorems.Thm_Formalism_L2_Th1_H_prod_blockSlice_firstBlockEmb
import Theorems.Thm_Formalism_L2_Th1_H_matrixForm_fourfoldBlock_firstBlockEmb

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
variable {n : Type*} [Fintype n]
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ) (hα0 : α 0 = 1)
    {P : (Fin 4 × n → ℂ) → ℂ}
    (hP : P ∈ Th (matH (blk4 h)) (fun x => ∏ a, α (slice a x)) (pow4 Λ))
    (z₁ : Fin 4 × n → ℂ) (hz₁ : slice 0 z₁ = 0) :
    (fun v => P (z₁ + emb0 v)) ∈ Th (matH h) α Λ := by
  refine ⟨?_, ?_⟩
  · intro v _
    exact (hP.1 (z₁ + emb0 v) (Set.mem_univ _)).comp_of_eq
      (analyticAt_const.add ((LinearMap.toContinuousLinearMap (emb0 (n := n))).analyticAt v)) rfl
  · intro x hx v
    have h1 := hP.2 (emb0 x) (firstBlockEmb_mem_fourfoldLattice Λ hx) (z₁ + emb0 v)
    simp only [opU, prod_blockSlice_firstBlockEmb α hα0, matrixForm_fourfoldBlock_firstBlockEmb, slice_add, hz₁, zero_add] at h1 ⊢
    rw [blockSlice_firstBlockEmb, if_pos rfl, blockSlice_firstBlockEmb, if_pos rfl, add_assoc, ← map_add] at h1
    exact h1
end Formalism.L2.Th1.H
