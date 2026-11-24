-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_submatrix_consRow_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:38.21869+00:00
-- url     : https://prove2.me/submissions/6ab913c9-ea4c-490a-9e04-49c5d73e46f8

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bCons_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5bCons_succ
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_consRow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_neg_one_pow_mul_neg_one_pow

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (Y : Matrix (Fin (n + 1)) (Fin (n + 2)) R)
    (u : Fin (n + 2) → R) (b₀ : Fin (n + 2)) (a : Fin (n + 1)) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by
  have e : (consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove =
      consRowMatrix (fun c => u (b₀.succAbove c))
        ((Y.submatrix id b₀.succAbove).submatrix a.succAbove id) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.submatrix_apply, Fin.succ_succAbove_zero, s5bCons_zero]
    · simp only [Matrix.submatrix_apply, Fin.succ_succAbove_succ, s5bCons_succ, id]
  rw [e, det_consRow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [cofVec, Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  have hs := neg_one_pow_mul_neg_one_pow (R := R) (a : ℕ)
  rw [pow_add]
  generalize (Y.submatrix a.succAbove (b₀.succAbove ∘ c.succAbove)).det = M
  linear_combination (-(u (b₀.succAbove c) * (-1) ^ (c : ℕ) * M)) * hs
end Formalism.HermitianLatticeCounting.P
