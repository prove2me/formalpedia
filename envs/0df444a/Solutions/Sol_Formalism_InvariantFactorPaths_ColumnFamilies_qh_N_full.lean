-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_N_full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:09.395088+00:00
-- url     : https://prove2.me/submissions/56389f43-41a1-4b3e-a6a7-fecfe73ce7cf

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhEquivOfCount
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qhDet_val


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
theorem _root_.solution (S : Finset (Fin n)) (hS : S.card = n) :
    qhN R n le_rfl (fun q => S.orderEmbOfFin hS q) = ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) := by
  have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS, Fintype.card_fin])
  have hid : ∀ q, S.orderEmbOfFin hS q = q := by
    intro q
    have hu := Finset.orderEmbOfFin_unique hS (f := id) (fun x => by rw [hSu]; exact Finset.mem_univ _) strictMono_id
    exact (congrFun hu q).symm
  have hc : ∀ p : Fin n, Fin.castLE (le_refl n) p = p := fun p => Fin.ext rfl
  unfold qhN
  rw [qhDet_val]
  congr 2
  ext p q
  first
    | (simp only [Matrix.of_apply, hid, hc]; done)
    | simp [genMat, hid, hc]
end Formalism.InvariantFactorPaths.ColumnFamilies
