-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_mem_strUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.297036+00:00
-- url     : https://prove2.me/submissions/b4286d96-9bad-4e54-8638-cb56728a38c2

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip

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
theorem _root_.solution {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := (Finset.mem_filter.1 h).2
end Formalism.InvariantFactorPaths.ColumnFamilies
