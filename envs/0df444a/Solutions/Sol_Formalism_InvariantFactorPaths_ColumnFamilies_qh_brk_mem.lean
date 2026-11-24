-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_brk_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:50:56.871645+00:00
-- url     : https://prove2.me/submissions/0b115b54-00bd-4c35-9257-8184f080636d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_weight_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mapCoord_brk
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_N_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_det_zpow_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_mem


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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    mapCoord R (brk mu I) ∈ inducedSections R mu := by
  rw [qh_mapCoord_brk]
  have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) (mu (lastIdx n)))
    (qh_prod_mem (R := R) (Finset.univ : Finset ↥(TCols mu))
      (fun c => qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q))
      (fun c => fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0)
      (fun c _ => qh_N_mem (R := R) (colH mu c) (colH_le mu c) _))
  first
    | (rw [qh_weight_sum hmu] at h; exact h)
    | (convert h using 2; exact (qh_weight_sum hmu).symm)
end Formalism.InvariantFactorPaths.ColumnFamilies
