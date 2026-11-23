-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_snoc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:33.280372+00:00
-- url     : https://prove2.me/submissions/48089d95-7151-4db2-9ae2-39e641a90a8b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} {R : Type} [CommRing R] {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hb : IsBlock h g1 t) {k : ℕ} (r c : Fin k → Fin m) :
    (h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).det =
      (t : R) * (g1.val.submatrix r c).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have h1 : ((h.val.submatrix (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (r a).castSucc) (Fin.last m))
      (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a => (c a).castSucc) (Fin.last m))).submatrix
        (Fin.last k).succAbove (Fin.last k).succAbove) = g1.val.submatrix r c := by
      ext a b
      simp [Fin.succAbove_last, hb.1]
    rw [h1]
    simp [hb.2.1, ← two_mul]
  · intro j _ hj
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
    simp [(hb.2.2 _).2]
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
