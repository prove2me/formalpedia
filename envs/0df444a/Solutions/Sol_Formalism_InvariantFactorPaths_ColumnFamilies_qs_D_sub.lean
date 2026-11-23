-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_D_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:33.271181+00:00
-- url     : https://prove2.me/submissions/ef70f3fb-8804-4308-8624-e82589407d36

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip

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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (lam kap : Fin n → ℤ) : qs_D lam kap ⊆ Finset.Ioc (lam (lastIdx n)) (kap 0) := Finset.filter_subset _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
