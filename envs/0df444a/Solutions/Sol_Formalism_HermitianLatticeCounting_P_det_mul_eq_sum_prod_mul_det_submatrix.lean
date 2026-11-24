-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_mul_eq_sum_prod_mul_det_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:37.694828+00:00
-- url     : https://prove2.me/submissions/a2c4606e-8f85-4202-b3ff-7e11b244c49a

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {t N : ℕ} (X : Matrix (Fin t) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin t) ℂ) :
    (X * Y).det = ∑ f : Fin t → Fin N, (∏ i, X i (f i)) * (Y.submatrix f id).det := by
  have h1 : (X * Y) = Matrix.of (fun i => ∑ k, X i k • Y k) := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [h1]
  have h2 := (Matrix.detRowAlternating (n := Fin t) (R := ℂ)).toMultilinearMap.map_sum
    (fun i k => X i k • Y k)
  have h3 : (Matrix.of (fun i => ∑ k, X i k • Y k)).det =
      ∑ f : Fin t → Fin N, Matrix.detRowAlternating (fun i => X i (f i) • Y (f i)) := h2
  rw [h3]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h4 := (Matrix.detRowAlternating (n := Fin t) (R := ℂ)).toMultilinearMap.map_smul_univ
    (fun i => X i (f i)) (fun i => Y (f i))
  exact h4
end Formalism.HermitianLatticeCounting.P
