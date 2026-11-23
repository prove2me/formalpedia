-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:33.236062+00:00
-- url     : https://prove2.me/submissions/ae144d58-3c32-4b15-8dd0-97b4a1872312

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_mem_strVert

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
theorem _root_.solution {mu nu : Fin n → ℤ} {b : ℕ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    mu (lastIdx n) + ((nu 0 - mu (lastIdx n)).toNat : ℕ) = nu 0 := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have := ((ql_mem_strVert h).1 0).1
  omega
end Formalism.InvariantFactorPaths.ColumnFamilies
