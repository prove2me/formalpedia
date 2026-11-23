-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_colH_low
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:52.003902+00:00
-- url     : https://prove2.me/submissions/0dc3fa2f-932d-4e77-b519-200ffeedcebd

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_le_last

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
theorem _root_.solution (hn : Dominant nu) {c : ℤ} (hc : c ≤ nu (lastIdx m)) : colH nu c = m := by
  rw [colH, Finset.filter_true_of_mem]
  · simp
  · intro a _; exact hc.trans (qr_le_last hn a)
end Formalism.InvariantFactorPaths.ColumnFamilies
