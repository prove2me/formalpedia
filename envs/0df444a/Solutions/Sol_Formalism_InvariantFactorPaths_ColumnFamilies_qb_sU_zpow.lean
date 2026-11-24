-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_sU_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:42.108256+00:00
-- url     : https://prove2.me/submissions/38ca3782-e4ab-43c2-bcba-5fb9c15a5828

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT

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
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (w : Fin n → ℤ) (z : ℤ) : qb_sU w ^ z = qb_sU (z • w) := by
  unfold qb_sU
  rw [← map_zpow, ← map_zpow, ofAdd_zsmul]
end Formalism.InvariantFactorPaths.ColumnFamilies
