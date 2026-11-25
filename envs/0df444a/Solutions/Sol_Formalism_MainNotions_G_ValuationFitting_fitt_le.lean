-- Prove2me | solution 1 for Formalism.MainNotions.G.ValuationFitting.fitt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:26:32.390432+00:00
-- url     : https://prove2.me/submissions/6ad580b4-e19a-48cb-8c50-637569d325ea

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_mul_submatrix_id
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
    ∀ g : Fin m → Fin h, v (algebraMap R C (α.submatrix id g).det) ≤ x := by
  intro g
  obtain ⟨P, Q, a', hP, hQ, hD, _, hx'⟩ := smith_data hv α hx
  have hα : P⁻¹ * (P * α * Q) * Q⁻¹ = α := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one]
  have hα' : α = P⁻¹ * (Matrix.diagonal a' * Em R m h * Q⁻¹) := by
    rw [← hD, ← Matrix.mul_assoc]
    exact hα.symm
  have e1 := hv.map_le_one (P⁻¹).det
  have e2 := hv.map_le_one ((Em R m h * Q⁻¹).submatrix id g).det
  rw [hα', mul_submatrix_id, Matrix.det_mul, Matrix.mul_assoc, mul_submatrix_id, Matrix.det_mul,
    Matrix.det_diagonal, ← hx']
  calc _ = v (algebraMap R C (P⁻¹).det) * ((∏ j, v (algebraMap R C (a' j))) *
        v (algebraMap R C ((Em R m h * Q⁻¹).submatrix id g).det)) := by
        simp only [map_mul, map_prod]
    _ ≤ 1 * ((∏ j, v (algebraMap R C (a' j))) * 1) := mul_le_mul' e1 (mul_le_mul' le_rfl e2)
    _ = _ := by rw [one_mul, mul_one]
end Formalism.MainNotions.G.ValuationFitting
