-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_lap_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:49.32987+00:00
-- url     : https://prove2.me/submissions/d6464af3-e7db-4a7a-9bbe-969277ff846d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mn_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_oe_succAbove
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_gt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sum_oe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {h : ℕ} (r : Fin (h + 1) → Fin n) (p : Fin (h + 1)) (I : Finset (Fin n)) (hI : I.card = h + 1)
    (A : Finset (Fin n)) (hA : A.card = h) (hr : ∀ i, r (p.succAbove i) = A.orderEmbOfFin hA i) :
    ∑ m ∈ I, ((qs_sg (I.erase m) m : ℤ) : R) * qs_mn g A (I.erase m) * g (r p) m =
      (-1) ^ (h - (p : ℕ)) * Matrix.det (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)) := by
  rw [Matrix.det_succ_row _ p, Finset.mul_sum, qs_sum_oe I hI]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (I.erase (I.orderEmbOfFin hI j)).card = h := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), hI]; rfl
  rw [qs_mn_eq g A _ hA hc, qs_sg, qs_card_gt I hI j]
  have hM : (Matrix.of fun a b : Fin (h + 1) => g (r a) (I.orderEmbOfFin hI b)).submatrix p.succAbove j.succAbove =
      Matrix.of fun a b : Fin h => g (A.orderEmbOfFin hA a) ((I.erase (I.orderEmbOfFin hI j)).orderEmbOfFin hc b) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply]
    rw [hr, qs_oe_succAbove I hI j hc]
  rw [hM]
  have hs : ((-1 : R)) ^ (h - (j : ℕ)) = (-1) ^ (h - (p : ℕ)) * (-1) ^ ((p : ℕ) + (j : ℕ)) := by
    rw [← pow_add]
    have hj := j.2; have hp := p.2
    have : h - (p : ℕ) + ((p : ℕ) + (j : ℕ)) = (h - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]; simp
  push_cast
  rw [hs]
  simp only [Matrix.of_apply]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
