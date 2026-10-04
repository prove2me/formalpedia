-- Prove2me | solution 1 for Conway99Formal.CubicMetric.cellDefect_table
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:07:20.022081+00:00
-- url     : https://prove2.me/submissions/c438b6a3-d690-4afc-8324-cb1e25eb8af1

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
theorem solution (p : Fin 13) :
    cellDefect p.val =
      ![60, 50, 40, 31, 23, 16, 10, 6, 3, 1, 0, 0, 0] p := by
  fin_cases p <;> norm_num [cellDefect, cellBound, minSquares]
