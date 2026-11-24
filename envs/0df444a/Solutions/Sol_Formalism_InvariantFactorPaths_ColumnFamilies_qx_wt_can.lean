-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_wt_can
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:46.644743+00:00
-- url     : https://prove2.me/submissions/7b99f788-e061-43dd-8898-2d8bbf72c3c1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_wtT_can


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
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (h : ps mu nu (K, k) (canT nu) ≠ 0) : qb_wtT mu K = nu - be k := by
  have h1 := qx_wt hd hmu hnu K k _ h
  rw [qb_wtT_can (hd.2.2.1 mu hmu nu hnu)] at h1
  rw [← h1, add_sub_cancel_right]
end Formalism.InvariantFactorPaths.ColumnFamilies
