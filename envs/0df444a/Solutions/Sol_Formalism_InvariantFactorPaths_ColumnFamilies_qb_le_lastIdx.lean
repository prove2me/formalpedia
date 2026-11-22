-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_le_lastIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:28.094141+00:00
-- url     : https://prove2.me/submissions/331ce0f6-f878-49f9-abba-c1afac1027ac

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (b : Fin n) : b ≤ lastIdx n := Fin.le_def.2 (by have := b.2; simp only [lastIdx]; omega)
end Formalism.InvariantFactorPaths.ColumnFamilies
