-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gc_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:35.904801+00:00
-- url     : https://prove2.me/submissions/7bb93274-b15d-45d3-96a6-26e91ee77025

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gc_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix InnerProductSpace
open scoped ComplexConjugate
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {l : ℕ} (y : Fin l → V) :
    (Matrix.of fun a b => inner ℂ (y a) (y b)).det = ∏ c, (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2 := by
  have hM : (Matrix.of fun a b => inner ℂ (y a) (y b)) =
      (gramSchmidtUnitriangularMatrix y).map conj * Matrix.diagonal (fun c => (‖gramSchmidt ℂ y c‖ : ℂ) ^ 2) * (gramSchmidtUnitriangularMatrix y)ᵀ := by
    ext a b
    rw [Matrix.of_apply, gc_inner, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
  have h1 : (gramSchmidtUnitriangularMatrix y).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [gramSchmidtUnitriangularMatrix]
    · intro i j hij
      have hij' : i < j := hij
      simp [gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]
  have h2 : ((gramSchmidtUnitriangularMatrix y).map conj).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [gramSchmidtUnitriangularMatrix]
    · intro i j hij
      have hij' : i < j := hij
      simp [gramSchmidtUnitriangularMatrix, hij'.ne', hij'.not_gt]
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, h2, Matrix.det_diagonal]
  simp
end Formalism.HermitianLatticeCounting.P
