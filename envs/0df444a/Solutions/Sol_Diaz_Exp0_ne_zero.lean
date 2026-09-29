-- Prove2me | solution 1 for Diaz.Exp0_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:08.739909+00:00
-- url     : https://prove2.me/submissions/c1972500-7edb-480a-b76c-b681a83b24b0

import Mathlib
import Definitions.Def_Diaz_Exponential

namespace Diaz

section
open ComplexConjugate

theorem Exp0_pos (x : ℚ × ℚ) : 0 < Exp0 x := Real.rpow_pos_of_pos (by norm_num) _
end

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution (x : ℚ × ℚ) : Exp0 x ≠ 0 := (Exp0_pos x).ne'
end
