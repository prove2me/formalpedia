-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_det_le_prod_row_norms
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:12.482271+00:00
-- url     : https://prove2.me/submissions/1826863f-122d-4ebb-9c3d-9fbb609afed8

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_gramSchmidt_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sqrt_det_gram_eq_prod_norm

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
theorem _root_.solution {j : ℕ} (N : Matrix (Fin j) (Fin j) ℂ) :
    ‖N.det‖ ≤ ∏ i, Real.sqrt (∑ k, ‖N i k‖ ^ 2) := by
  let a : Fin j → EuclideanSpace ℂ (Fin j) := fun i => WithLp.toLp 2 (N i)
  have hg : Matrix.gram ℂ a = ((starRingEnd ℂ).mapMatrix N) * Nᵀ := by
    ext p q
    simp [Matrix.gram_apply, a, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hdet : ‖(Matrix.gram ℂ a).det‖ = ‖N.det‖ ^ 2 := by
    rw [hg, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, RCLike.norm_conj]
    ring
  have h1 := sqrt_det_gram_eq_prod_norm a
  rw [hdet, Real.sqrt_sq (norm_nonneg _)] at h1
  rw [h1]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  refine (norm_gramSchmidt_le a i).trans (le_of_eq ?_)
  simp [a, EuclideanSpace.norm_eq]
end Formalism.HermitianLatticeCounting.P
