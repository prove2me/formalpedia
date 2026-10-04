-- Prove2me | solution 1 for Conway99Formal.CubicMetric.cellDefect_supporting_line
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:07:19.353986+00:00
-- url     : https://prove2.me/submissions/773eb073-9d4c-4bc8-be58-fc7ab11f06ef

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

namespace Conway99Formal.CubicMetric














































end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

open Conway99Formal.CubicMetric in
theorem solution (p : Fin 13) (hp : p.val < 10) :
    7 * (10 - (p.val : ℤ)) - 19 ≤ cellDefect p.val := by
  fin_cases p <;> norm_num [cellDefect, cellBound, minSquares] at *
