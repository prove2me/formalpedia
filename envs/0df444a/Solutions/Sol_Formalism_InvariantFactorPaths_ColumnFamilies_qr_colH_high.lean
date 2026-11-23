-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_colH_high
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:51.574501+00:00
-- url     : https://prove2.me/submissions/ae5d73ce-acd7-48fc-9fb0-b5e9346a2639

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_le_zero

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
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hn : Dominant nu) {c : ℤ} (hc : nu 0 < c) : colH nu c = 0 := by
  rw [colH, Finset.filter_false_of_mem]
  · simp
  · intro a _; exact not_le.2 (lt_of_le_of_lt (qr_le_zero hn a) hc)
end Formalism.InvariantFactorPaths.ColumnFamilies
