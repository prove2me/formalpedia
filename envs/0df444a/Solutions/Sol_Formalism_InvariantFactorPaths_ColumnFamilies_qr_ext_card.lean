-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_ext_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:00.176172+00:00
-- url     : https://prove2.me/submissions/f4c8c30c-2def-493c-ba7e-a899c9753801

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_last_notMem

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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : (qr_ext e S).card = S.card + if e then 1 else 0 := by
  unfold qr_ext
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (qr_last_notMem S), Finset.card_map]
  · rw [Finset.card_map]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
