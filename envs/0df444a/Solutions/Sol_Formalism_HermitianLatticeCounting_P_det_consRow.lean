-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_consRow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:33.75564+00:00
-- url     : https://prove2.me/submissions/2e2c427d-8ad2-4901-85d2-406c236f6b62

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bCons_zero

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
theorem _root_.solution {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) :
    (consRowMatrix u Y).det = ∑ b, u b * cofVec Y b := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : (consRowMatrix u Y).submatrix Fin.succ b.succAbove =
      Y.submatrix id b.succAbove := by
    ext i j; rfl
  rw [this, s5bCons_zero]; simp only [cofVec]; ring
end Formalism.HermitianLatticeCounting.P
