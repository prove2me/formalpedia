-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_mem_strVert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:34.678851+00:00
-- url     : https://prove2.me/submissions/7962c221-de26-4978-842c-d853f3862d95

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip

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
theorem _root_.solution {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strVert mu b) :
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  simpa only [strVert, mem_filter, Fintype.mem_piFinset, mem_Icc] using h
end Formalism.InvariantFactorPaths.ColumnFamilies
