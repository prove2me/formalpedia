-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:17.112158+00:00
-- url     : https://prove2.me/submissions/68e4b980-6ccc-416f-b21b-82dec43a16e5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd

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
theorem _root_.solution (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) (c : ↥D) :
    qs_add D K m c.1 = insert (m c) (K c.1) := by simp [qs_add, c.2]
end Formalism.InvariantFactorPaths.ColumnFamilies
