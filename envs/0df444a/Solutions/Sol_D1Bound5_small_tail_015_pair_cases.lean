-- Prove2me | solution 1 for D1Bound5.small_tail_015_pair_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:14.698594+00:00
-- url     : https://prove2.me/submissions/c4d4c9ac-2e76-4f85-ac95-6c5973fe889b

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions

section
namespace D1Bound5
open QuadInt

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- For omega^2 = -15, the large compatible ordered pairs in the
closed norm-15 disk are exactly the opposite imaginary elements. -/
theorem _root_.solution :
    ∀ b ∈ disk 0 15 15, ∀ c ∈ disk 0 15 15,
      9 ≤ b.norm → b.norm ≤ c.norm → b ≠ c →
      hasSquareRoot (b*c+1) = true →
      (b = (⟨0,-1⟩ : QuadInt 0 15) ∧ c = ⟨0,1⟩) ∨
      (b = (⟨0,1⟩ : QuadInt 0 15) ∧ c = ⟨0,-1⟩) := by
  decide +kernel





end D1Bound5
end
