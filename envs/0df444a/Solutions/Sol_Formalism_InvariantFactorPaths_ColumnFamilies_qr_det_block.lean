-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_det_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:49.085702+00:00
-- url     : https://prove2.me/submissions/beb17035-68a2-4d1a-a168-d930f123fbe6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_snoc

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
theorem _root_.solution (hb : IsBlock h g1 t) : h.val.det = (t : R) * g1.val.det := by
  have := qr_det_snoc hb (id : Fin m → Fin m) id
  have h1 : (Fin.snoc (α := fun _ => Fin (m + 1)) (fun a : Fin m => (id a).castSucc) (Fin.last m)) = id := by
    funext a
    induction a using Fin.lastCases <;> simp
  rw [h1] at this
  simpa using this
end Formalism.InvariantFactorPaths.ColumnFamilies
