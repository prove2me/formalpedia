-- Prove2me | solution 1 for D1Bound5.smallTriple_classified_rectangular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:38.782695+00:00
-- url     : https://prove2.me/submissions/e5b734ba-1d90-42f7-919e-155367c953d9

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_smallTriple_classified_0_1
import Theorems.Thm_D1Bound5_smallTriple_classified_0_2
import Theorems.Thm_D1Bound5_smallTriple_classified_0_3
import Theorems.Thm_D1Bound5_smallTriple_classified_0_4
import Theorems.Thm_D1Bound5_smallTriple_classified_0_5
import Theorems.Thm_D1Bound5_smallTriple_classified_0_6
import Theorems.Thm_D1Bound5_smallTriple_classified_0_7
import Theorems.Thm_D1Bound5_smallTriple_classified_0_8
import Theorems.Thm_D1Bound5_smallTriple_classified_1_1
import Theorems.Thm_D1Bound5_smallTriple_classified_1_2
import Theorems.Thm_D1Bound5_smallTriple_classified_1_3
import Theorems.Thm_D1Bound5_smallTriple_classified_1_4
import Theorems.Thm_D1Bound5_smallTriple_classified_1_5
import Theorems.Thm_D1Bound5_smallTriple_classified_1_6
import Theorems.Thm_D1Bound5_smallTriple_classified_1_7
import Theorems.Thm_D1Bound5_smallTriple_classified_1_8

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


























































































theorem _root_.solution {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hlo : 1 ≤ nu) (hhi : nu ≤ 8)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable tau nu := by
  rcases htau with rfl | rfl
  · interval_cases nu
    · exact smallTriple_classified_0_1 t ht hnorm
    · exact smallTriple_classified_0_2 t ht hnorm
    · exact smallTriple_classified_0_3 t ht hnorm
    · exact smallTriple_classified_0_4 t ht hnorm
    · exact smallTriple_classified_0_5 t ht hnorm
    · exact smallTriple_classified_0_6 t ht hnorm
    · exact smallTriple_classified_0_7 t ht hnorm
    · exact smallTriple_classified_0_8 t ht hnorm
  · interval_cases nu
    · exact smallTriple_classified_1_1 t ht hnorm
    · exact smallTriple_classified_1_2 t ht hnorm
    · exact smallTriple_classified_1_3 t ht hnorm
    · exact smallTriple_classified_1_4 t ht hnorm
    · exact smallTriple_classified_1_5 t ht hnorm
    · exact smallTriple_classified_1_6 t ht hnorm
    · exact smallTriple_classified_1_7 t ht hnorm
    · exact smallTriple_classified_1_8 t ht hnorm

end D1Bound5
end
