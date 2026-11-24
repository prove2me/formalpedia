-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.det_rows_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:31.514428+00:00
-- url     : https://prove2.me/submissions/67945f40-fd78-40fd-b446-aa2892954957

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_emb_succAbove
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_emb
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sum_emb

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {d : ℕ} (m : Matrix (Fin n) (Fin n) R) (r : Fin (d + 1) → Fin n) (i : Fin (d + 1))
    {I' J : Finset (Fin n)} (hJ : J.card = d + 1) (hI' : I'.card = d)
    (hr : (fun x => r (i.succAbove x)) = I'.orderEmbOfFin hI') :
    (-1 : R) ^ (d + (i : ℕ)) * (m.submatrix r (J.orderEmbOfFin hJ)).det =
      ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m (r i) b := by
  rw [sum_emb hJ, Matrix.det_succ_row _ i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcard : (J.erase (J.orderEmbOfFin hJ j)).card = d := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem J hJ j), hJ]
    rfl
  rw [sg_emb hJ j, minorF_eq m hI' hcard, ← emb_succAbove hJ j rfl hcard, ← hr]
  simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_def]
  push_cast
  have e : ((-1 : R) ^ (d + (i : ℕ))) * (-1) ^ ((i : ℕ) + (j : ℕ)) = (-1) ^ (d + (j : ℕ)) := by
    rw [← pow_add, show d + (i : ℕ) + ((i : ℕ) + (j : ℕ)) = d + j + 2 * i by ring, pow_add, pow_mul]
    simp
  linear_combination (m (r i) (J.orderEmbOfFin hJ j) *
    (m.submatrix (fun x => r (i.succAbove x)) (fun x => J.orderEmbOfFin hJ (j.succAbove x))).det) * e
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
