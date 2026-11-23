-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_le_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:12.986818+00:00
-- url     : https://prove2.me/submissions/03341dc9-0072-475e-b574-feafdfc175b4

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral

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
theorem _root_.solution (hn : Dominant nu) (a : Fin m) : nu (lastIdx m) ≤ nu a := by
  apply hn
  rw [Fin.le_def]
  show a.1 ≤ m - 1
  have := a.2
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
