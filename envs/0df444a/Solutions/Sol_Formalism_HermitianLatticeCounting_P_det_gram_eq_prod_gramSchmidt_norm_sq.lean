-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_gram_eq_prod_gramSchmidt_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:37.480409+00:00
-- url     : https://prove2.me/submissions/42de9709-5280-424c-88fd-5ecbe3907fc4

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_gramSchmidt_coeff_eq_one
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eq_sum_gramSchmidt_coeff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_sesquilinear_change_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (a : Fin r → U) :
    (Matrix.gram ℂ a).det = ∏ i, ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2) := by
  have e : Matrix.gram ℂ a = (Matrix.of fun p q => (innerₛₗ ℂ).flip
      (∑ i, s5bL a p i • gramSchmidt ℂ a i) (∑ k, s5bL a q k • gramSchmidt ℂ a k))ᵀ := by
    ext p q
    simp only [Matrix.transpose_apply, Matrix.of_apply, ← eq_sum_gramSchmidt_coeff, Matrix.gram_apply]; rfl
  rw [e, Matrix.det_transpose, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one]
  have : (Matrix.of fun i k => (innerₛₗ ℂ).flip (gramSchmidt ℂ a i) (gramSchmidt ℂ a k)) =
      Matrix.diagonal fun i => ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2) := by
    ext i k
    by_cases h : i = k
    · subst h; simp [inner_self_eq_norm_sq_to_K]
    · simp [Matrix.diagonal_apply_ne _ h, gramSchmidt_orthogonal ℂ a (Ne.symm h)]
  rw [this, Matrix.det_diagonal]; simp
end Formalism.HermitianLatticeCounting.P
