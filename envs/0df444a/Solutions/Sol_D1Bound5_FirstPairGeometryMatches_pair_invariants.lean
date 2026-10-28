-- Prove2me | solution 1 for D1Bound5.FirstPairGeometryMatches.pair_invariants
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:33.227977+00:00
-- url     : https://prove2.me/submissions/ccdb7911-d865-4a61-8120-4b0534840a5c

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5

/-- Matching coordinate pairs have identical exact squared norms and
separation, even though the unused third coordinate differs. -/
theorem _root_.solution
    (g : FirstPairGeometryRow) (r : OneSmallCutoffRow)
    (h : FirstPairGeometryMatches g r) :
    g.a0 = r.a0 ∧ g.b0 = r.b0 ∧ g.dab = r.dab := by
  rcases h with ⟨ht,hn,ha,hb,_⟩
  simp [FirstPairGeometryRow.a0,FirstPairGeometryRow.b0,FirstPairGeometryRow.dab,
    FirstPairGeometryRow.anchorA,FirstPairGeometryRow.anchorB,
    OneSmallCutoffRow.a0,OneSmallCutoffRow.b0,OneSmallCutoffRow.dab,
    OneSmallTripleRow.anchorA,OneSmallTripleRow.anchorB,
    QuadraticAlgebra.norm,ht,hn,ha,hb]



end D1Bound5
end
