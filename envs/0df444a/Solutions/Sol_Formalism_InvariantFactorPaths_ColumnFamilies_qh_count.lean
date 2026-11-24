-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.114707+00:00
-- url     : https://prove2.me/submissions/2d7d8b02-67d9-4da2-82b4-c5694dc7fff3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_lt_colH_iff

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
theorem _root_.solution [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) :
    ((TCols mu).filter (fun c => t.val < colH mu c)).card = (mu t - mu (lastIdx n)).toNat := by
  have h0 : mu t ≤ mu 0 := hmu (by first | exact Fin.zero_le _ | (rw [Fin.le_iff_val_le_val]; simp))
  have hset : (TCols mu).filter (fun c => t.val < colH mu c) =
      Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    simp only [Finset.mem_filter, qh_lt_colH_iff hmu, TCols, Finset.mem_Ioc]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans h0⟩, hh.2⟩⟩
  rw [hset, Int.card_Ioc]
end Formalism.InvariantFactorPaths.ColumnFamilies
