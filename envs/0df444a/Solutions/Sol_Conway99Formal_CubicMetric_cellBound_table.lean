-- Prove2me | solution 1 for Conway99Formal.CubicMetric.cellBound_table
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:06:38.883808+00:00
-- url     : https://prove2.me/submissions/48da0633-8d92-4947-a330-b7d9246372f4

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
    cellBound p.val =
      ![879, 735, 595, 471, 359, 255, 171, 115, 79, 51, 35, 35, 39] p := by
  fin_cases p <;> norm_num [cellBound, minSquares]
