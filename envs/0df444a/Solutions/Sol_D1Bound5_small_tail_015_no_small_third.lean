-- Prove2me | solution 1 for D1Bound5.small_tail_015_no_small_third
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:46.960988+00:00
-- url     : https://prove2.me/submissions/d024e59f-01f5-414d-af29-d5e9fde44806

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



/-- Neither opposite imaginary pair has a compatible nonzero third
entry of norm at most fifteen. -/
theorem _root_.solution :
    ∀ a ∈ disk 0 15 15, a ≠ 0 →
      hasSquareRoot (a*(⟨0,-1⟩ : QuadInt 0 15)+1) = false ∨
      hasSquareRoot (a*(⟨0,1⟩ : QuadInt 0 15)+1) = false := by
  decide +kernel



end D1Bound5
end
