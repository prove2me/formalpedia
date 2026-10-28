-- Prove2me | solution 1 for D1Bound5.oneSmallFixedRows_cutoff_member
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:19.663393+00:00
-- url     : https://prove2.me/submissions/a05cd969-0cc6-4032-b07c-b907695f9d40

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Theorems.Thm_D1Bound5_oneSmallCutoffRows_triples

section
namespace D1Bound5

/-- The finite triple classifier supplies an actual member of the
analytic cutoff table, rather than just an isolated valid record. -/
theorem _root_.solution (r : OneSmallTripleRow)
    (hr : r ∈ oneSmallFixedRows) :
    ∃ c ∈ oneSmallCutoffRows, c.triple = r := by
  have hm : r ∈ (oneSmallCutoffRows.map OneSmallCutoffRow.triple).toFinset := by
    rw [oneSmallCutoffRows_triples]
    exact Finset.mem_insert_of_mem hr
  have hl : r ∈ oneSmallCutoffRows.map OneSmallCutoffRow.triple := by
    simpa only [List.mem_toFinset] using hm
  exact List.mem_map.mp hl

end D1Bound5
end
