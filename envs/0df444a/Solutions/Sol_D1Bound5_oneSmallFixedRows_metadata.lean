-- Prove2me | solution 1 for D1Bound5.oneSmallFixedRows_metadata
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:14.802355+00:00
-- url     : https://prove2.me/submissions/19b3e6d0-8e11-4f1d-a3f5-eba6bb112593

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
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt

/-- Exact metadata used when joining the finite fourth-entry certificates to
the analytic retained-triple argument. Every assertion is checked directly
on all 56 manuscript rows. -/
theorem _root_.solution :
    ∀ r ∈ oneSmallFixedRows,
      1024 ≤ r.cutoff ∧
      (r.anchorA.norm = 1 ∨ r.anchorA.norm = 2) ∧
      9 ≤ r.anchorB.norm ∧
      (r.anchorA.norm = 2 →
        4*r.anchorA.norm*r.anchorB.norm*r.anchorS.norm < r.cutoff) := by
  decide +kernel

end D1Bound5
end
