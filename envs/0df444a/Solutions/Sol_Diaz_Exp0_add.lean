-- Prove2me | solution 1 for Diaz.Exp0_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:08.207491+00:00
-- url     : https://prove2.me/submissions/4ec27b7d-ffa0-45b6-947c-09bc948d70fa

import Mathlib
import Definitions.Def_Diaz_Exponential

namespace Diaz

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution (x y : ℚ × ℚ) : Exp0 (x + y) = Exp0 x * Exp0 y := by
  simp only [Exp0, Prod.fst_add, Prod.snd_add]
  rw [← Real.rpow_add (by norm_num)]
  push_cast
  ring_nf
end
