-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_be_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:54.291447+00:00
-- url     : https://prove2.me/submissions/82a5506d-2b8a-4315-9aa3-43865ab2d148

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LamStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_be_apply

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
theorem _root_.solution (b : ℕ) : Function.Injective (ql_be (n := n) b) := by
  intro L L' h
  apply Subtype.ext
  ext a
  have := congrFun h a
  rw [ql_be_apply, ql_be_apply] at this
  by_cases h1 : a ∈ L.1 <;> by_cases h2 : a ∈ L'.1 <;> simp_all
end Formalism.InvariantFactorPaths.ColumnFamilies
