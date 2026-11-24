-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strDown
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:40.248445+00:00
-- url     : https://prove2.me/submissions/a5650ae0-daa4-4230-89ce-ae5adbb6a38b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip

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
omit [NeZero n]
open Classical
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strDown mu b) : HStrip nu mu b :=
  (Finset.mem_filter.1 h).2
end Formalism.InvariantFactorPaths.ColumnFamilies
