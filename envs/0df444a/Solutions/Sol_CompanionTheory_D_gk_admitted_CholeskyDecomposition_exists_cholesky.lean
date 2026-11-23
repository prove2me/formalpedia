-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:42.491847+00:00
-- url     : https://prove2.me/submissions/0415966e-00d2-4d5c-97d0-df66ed1043b9

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_exists_isUpperTriangular_conjTranspose_mul_self
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_star_mul_self_norm_div

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
    ∃ B : Matrix n n 𝕜, ∃ a : n → ℝ, B.IsUpperTriangular ∧ (∀ i, 0 < a i) ∧
      (∀ i, B i i = a i) ∧ Bᴴ * B = S := by
  obtain ⟨R, hR, hRS⟩ := exists_isUpperTriangular_conjTranspose_mul_self hS
  have hdet : S.det ≠ 0 := (isUnit_iff_isUnit_det S).1 hS.isUnit |>.ne_zero
  have hRi : ∀ i, R i i ≠ 0 := by
    have : R.det ≠ 0 := by
      intro h; apply hdet; rw [← hRS, det_mul, h, mul_zero]
    rw [det_of_isUpperTriangular hR] at this
    exact fun i => Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)
  refine ⟨diagonal (fun i => (‖R i i‖ : 𝕜) / R i i) * R, fun i => ‖R i i‖,
    (blockTriangular_diagonal _).mul hR, fun i => norm_pos_iff.2 (hRi i), fun i => ?_, ?_⟩
  · rw [diagonal_mul, div_mul_cancel₀ _ (hRi i)]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _)ᴴ,
      diagonal_conjTranspose, diagonal_mul_diagonal]
    have : (fun i => (star (fun i => (‖R i i‖ : 𝕜) / R i i)) i * ((‖R i i‖ : 𝕜) / R i i)) =
        fun _ => 1 := funext fun i => star_mul_self_norm_div (hRi i)
    rw [this, diagonal_one, Matrix.one_mul, hRS]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
