-- Prove2me | solution 1 for Formalism.MainNotions.G.ValuationFitting.fitt_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:25:58.359009+00:00
-- url     : https://prove2.me/submissions/8df8b6e6-211c-4e69-9d5b-35a368c0b709

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_det_mul_mem_fitt0
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_mul_submatrix_id
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_Em_castLE
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_smith_data
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace Formalism.MainNotions.G.ValuationFitting
theorem _root_.solution (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ y ∈ Formalism.L2.FormalSeriesBounds.S4.fitt0 α, v (algebraMap R C y) = x := by
  obtain ⟨P, Q, a', hP, hQ, hD, hz, hx'⟩ := smith_data hv α hx
  by_cases hmh : m ≤ h
  · refine ⟨(α * Q.submatrix id (Fin.castLE hmh)).det, det_mul_mem_fitt0 _ _, ?_⟩
    have hαQ : α * Q = P⁻¹ * (Matrix.diagonal a' * Em R m h) := by
      rw [← hD, Matrix.mul_assoc P α Q, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    rw [← mul_submatrix_id, hαQ, mul_submatrix_id, mul_submatrix_id, Em_castLE hmh, Matrix.mul_one,
      Matrix.det_mul, Matrix.det_diagonal]
    simp only [map_mul, map_prod]
    rw [hv.one_of_isUnit (Matrix.isUnit_nonsing_inv_det P hP), one_mul, hx']
  · push_neg at hmh
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [map_zero, map_zero, ← hx']
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ ⟨h, hmh⟩)
    rw [hz ⟨h, hmh⟩ le_rfl, map_zero, map_zero]
end Formalism.MainNotions.G.ValuationFitting
