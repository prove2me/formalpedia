-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_G_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:15.240562+00:00
-- url     : https://prove2.me/submissions/01c29966-35c4-4606-a689-8672675cd409

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_colH_high


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
theorem _root_.solution (hn : Dominant nu) (K' I' : TIdx nu) {c : ℤ} (hc : nu 0 < c) :
    qr_G g1 K' I' c = 1 :=
  qr_det_empty _ (qr_colH_high hn hc) _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
