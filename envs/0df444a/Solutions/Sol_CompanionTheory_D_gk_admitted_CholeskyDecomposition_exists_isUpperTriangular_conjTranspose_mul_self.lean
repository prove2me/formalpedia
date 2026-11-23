-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_isUpperTriangular_conjTranspose_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:48.391367+00:00
-- url     : https://prove2.me/submissions/c49b8017-ad2c-473c-90e3-19ae57d474ab

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_isUpperTriangular_conjTranspose_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {S : Matrix n n 𝕜} (hS : S.PosDef) :
    ∃ R : Matrix n n 𝕜, R.IsUpperTriangular ∧ Rᴴ * R = S := by
  have hLi : (LDL.lowerInv hS).IsLowerTriangular := fun i j hij =>
    LDL.lowerInv_triangular hS (OrderDual.toDual_lt_toDual.1 hij)
  have hL : (LDL.lower hS).IsLowerTriangular := blockTriangular_inv_of_blockTriangular hLi
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 (isUnit_of_invertible (LDL.lowerInv hS)))
  have hpos : ∀ i, 0 < LDL.diagEntries hS i := fun i => by
    simpa [LDL.diag] using hD.diag_pos (i := i)
  set d : n → ℝ := fun i => RCLike.re (LDL.diagEntries hS i)
  have hd : ∀ i, LDL.diagEntries hS i = (d i : 𝕜) := fun i => by
    obtain ⟨_, him⟩ := RCLike.pos_iff.1 (hpos i)
    rw [← RCLike.re_add_im (LDL.diagEntries hS i), him]; simp [d]
  have hd0 : ∀ i, 0 ≤ d i := fun i => (RCLike.pos_iff.1 (hpos i)).1.le
  refine ⟨diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ,
    (blockTriangular_diagonal _).mul (isUpperTriangular_conjTranspose_iff.2 hL), ?_⟩
  have hsq : (diagonal (fun i => (Real.sqrt (d i) : 𝕜)))ᴴ * diagonal (fun i => (Real.sqrt (d i) : 𝕜))
      = LDL.diag hS := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, LDL.diag]
    congr 1; funext i
    rw [hd i, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hd0 i)]
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  calc LDL.lower hS * (diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        (diagonal (fun i => (Real.sqrt (d i) : 𝕜)) * (LDL.lower hS)ᴴ)
      = LDL.lower hS * ((diagonal fun i => (Real.sqrt (d i) : 𝕜))ᴴ *
        diagonal (fun i => (Real.sqrt (d i) : 𝕜))) * (LDL.lower hS)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = S := by rw [hsq, LDL.lower_conj_diag]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
