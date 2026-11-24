-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_filter_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.314767+00:00
-- url     : https://prove2.me/submissions/4ee3ae85-5d70-4707-915e-c952e2a013eb

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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : ((qr_ext e S).filter (· ≤ Fin.last m)) = qr_ext e S := by
  apply Finset.filter_true_of_mem
  intro x _; exact Fin.le_last x
end Formalism.InvariantFactorPaths.ColumnFamilies
