-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:38.113804+00:00
-- url     : https://prove2.me/submissions/e732b486-0ef8-4918-977f-6e295b8c8c80

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_submatrix_mul_castLE_of_lower
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_submatrix_castLE_of_unitUpper

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
theorem _root_.solution : CramerUpper := by
  intro R _ N l hl Lo W Up hL1 hL0 hU1 hU0 hW c b hc
  have hLo' : ∀ i j : Fin N, (i : ℕ) < l → l ≤ (j : ℕ) → Lo i j = 0 := fun i j hi hj =>
    hL0 i j (by rw [Fin.lt_def]; omega)
  have key : ∀ {α : Type} (g : α → Fin N), (Lo * W * Up).submatrix (Fin.castLE hl) g =
      Lo.submatrix (Fin.castLE hl) (Fin.castLE hl) * (W.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Up.submatrix (Fin.castLE hl) g) := by
    intro α g
    rw [Matrix.mul_assoc, submatrix_mul_castLE_of_lower hl Lo (W * Up) g hLo', submatrix_mul_castLE_of_lower hl W Up g hW]
  rw [key, key, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_submatrix_castLE_of_unitUpper hl Up hU1 hU0]
  set A := Up.submatrix (Fin.castLE hl) (Fin.castLE hl) with hA
  have hAdet : A.det = 1 := det_submatrix_castLE_of_unitUpper hl Up hU1 hU0
  set u : Fin l → R := fun k => Up (Fin.castLE hl k) b with hu
  have e1 : Up.submatrix (Fin.castLE hl) (fun j => if j = c then b else Fin.castLE hl j) =
      A.updateCol c u := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.updateCol_apply, hA, hu]
    split_ifs <;> rfl
  have hrow : ∀ j, A c j = if j = c then 1 else 0 := by
    intro j
    rcases lt_trichotomy j c with h | h | h
    · rw [if_neg h.ne]; exact hU0 _ _ (by simpa using h)
    · subst h; simp [hA, hU1]
    · rw [if_neg h.ne']; exact hc j h
  have hadj : ∀ k, A.adjugate c k = if k = c then 1 else 0 := by
    intro k
    have h1 : (A * A.adjugate) c k = (1 : Matrix (Fin l) (Fin l) R) c k := by
      rw [Matrix.mul_adjugate, hAdet, one_smul]
    rw [Matrix.mul_apply] at h1
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [h1, Matrix.one_apply]
    simp only [eq_comm]
  have e2 : (A.updateCol c u).det = u c := by
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct]
    simp [hadj]
  rw [e1, e2]; ring
end Formalism.HermitianLatticeCounting.P
