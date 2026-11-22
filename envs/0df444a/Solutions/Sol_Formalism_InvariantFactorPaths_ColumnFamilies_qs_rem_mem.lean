-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:01.603474+00:00
-- url     : https://prove2.me/submissions/5f94cf1d-2b99-4e67-a5c6-bd2bb504a4b5

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
    qs_rem D K m c.1 = (K c.1).erase (m c) := by simp [qs_rem, c.2]
end Formalism.InvariantFactorPaths.ColumnFamilies
