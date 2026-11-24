-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_G_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:50.772027+00:00
-- url     : https://prove2.me/submissions/81d0c90b-6cce-41ba-b8d0-c29f0db699e1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_full
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_colH_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_subsing


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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ} {R : Type} [CommRing R]
  {h : GL (Fin (m + 1)) R} {g1 : GL (Fin m) R} {t : Rˣ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) :
    qr_G g1 K' I' c = g1.val.det := by
  have h1 : c ∉ TCols nu := by
    simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt]; exact Or.inl hc
  have := qr_subsing hn h1
  rw [qr_G, Subsingleton.elim (qr_base K' c) (qr_base I' c)]
  exact qr_det_full _ (qr_colH_low hn hc) _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
