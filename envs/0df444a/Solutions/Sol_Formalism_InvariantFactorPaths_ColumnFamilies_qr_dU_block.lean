-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_dU_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:50.768797+00:00
-- url     : https://prove2.me/submissions/3f03b8bb-48be-4c4e-95f1-d54c1827f029

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_dU_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_det_block


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
theorem _root_.solution (hb : IsBlock h g1 t) : qc_dU h = t * qc_dU g1 := by
  apply Units.ext
  rw [Units.val_mul, qc_dU_coe, qc_dU_coe, qr_det_block hb]
end Formalism.InvariantFactorPaths.ColumnFamilies
