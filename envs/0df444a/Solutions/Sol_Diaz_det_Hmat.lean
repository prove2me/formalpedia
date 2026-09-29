-- Prove2me | solution 1 for Diaz.det_Hmat
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:12.585347+00:00
-- url     : https://prove2.me/submissions/d5bb22ad-ade1-4330-abbd-e4279a8a44da

import Mathlib
import Definitions.Def_Diaz_Rigidity

namespace Diaz

end Diaz

section
open ComplexConjugate
variable {K : Subfield ℂ} {u r : ℂ}

open Diaz in
theorem solution (h : u * conj u = r ^ 2) : (Hmat u r).det = 0 := by
  rw [Hmat, Matrix.det_fin_two_of, h]; ring
end
