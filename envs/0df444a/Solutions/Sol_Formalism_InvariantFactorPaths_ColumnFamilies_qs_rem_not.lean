-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_rem_not
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:29.715188+00:00
-- url     : https://prove2.me/submissions/07bdd284-f3a2-4ec0-8d71-75bd9e74747e

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
theorem _root_.solution (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) {c : ℤ} (hc : c ∉ D) :
    qs_rem D K m c = K c := by simp [qs_rem, hc]
end Formalism.InvariantFactorPaths.ColumnFamilies
