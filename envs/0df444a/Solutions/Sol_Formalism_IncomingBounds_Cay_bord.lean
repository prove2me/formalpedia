-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.bord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:03.406538+00:00
-- url     : https://prove2.me/submissions/36662a9c-6e93-4fb6-a2d9-6b4d74dd3d5e

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {R : Type*} [CommRing R] (k : ℕ) (B : Matrix (Fin (k+2)) (Fin (k+2)) R) (j : Fin (k+2)) :
    ∑ q : Fin (k+1), ∑ p : Fin (k+1),
        adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 * B j q.succ
      = B j 0 * (B.submatrix j.succAbove Fin.succ).det - (-1) ^ (j : ℕ) * B.det := by
  have hcol : ∀ q : Fin (k+1), ∑ p : Fin (k+1),
      adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 =
      (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det := by
    intro q
    have h1 : ∑ p : Fin (k+1), adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 =
        cramer (B.submatrix j.succAbove Fin.succ) (fun p => B (j.succAbove p) 0) q := by
      rw [cramer_eq_adjugate_mulVec]; rfl
    have h2 : (B.submatrix j.succAbove Fin.succ).updateCol q (fun p => B (j.succAbove p) 0) =
        (B.submatrix j.succAbove q.succ.succAbove).submatrix id q.cycleRange := by
      ext x y
      simp only [Matrix.updateCol_apply, Matrix.submatrix_apply, id_eq, Fin.succAbove_cycleRange,
        Equiv.swap_apply_def]
      by_cases hy : y = q
      · subst hy; simp
      · have hs : y.succ ≠ q.succ := fun h => hy (Fin.succ_injective _ h)
        simp [hy, hs, Fin.succ_ne_zero]
    rw [h1, cramer_apply, h2, det_permute', Fin.sign_cycleRange]
    simp
  have hL : ∑ q : Fin (k+1), ∑ p : Fin (k+1),
      adjugate (B.submatrix j.succAbove Fin.succ) q p * B (j.succAbove p) 0 * B j q.succ =
      ∑ q : Fin (k+1), (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det *
        B j q.succ := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_mul, hcol q]
  rw [hL, det_succ_row B j, Fin.sum_univ_succ (n := k+1), Fin.succAbove_zero]
  simp only [Fin.val_zero, Fin.val_succ, add_zero, mul_add, Finset.mul_sum]
  have e1 : (-1 : R) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := by rw [← mul_pow]; simp
  have hsum : ∑ q : Fin (k+1), (-1 : R) ^ (j : ℕ) * ((-1) ^ ((j : ℕ) + ((q : ℕ) + 1)) * B j q.succ *
      (B.submatrix j.succAbove q.succ.succAbove).det) =
      -∑ q : Fin (k+1), (-1 : R) ^ (q : ℕ) * (B.submatrix j.succAbove q.succ.succAbove).det *
        B j q.succ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    linear_combination
      (-(-1 : R) ^ (q : ℕ) * B j q.succ * (B.submatrix j.succAbove q.succ.succAbove).det) * e1
  rw [hsum]
  linear_combination (B j 0 * (B.submatrix j.succAbove Fin.succ).det) * e1
end Formalism.IncomingBounds.Cay
