-- Prove2me | solution 1 for Diaz.Exp0_swap_conj
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:09.690453+00:00
-- url     : https://prove2.me/submissions/08b7117e-3be0-46c4-a329-47ba0a5ab9a1

import Mathlib
import Definitions.Def_Diaz_Exponential

namespace Diaz

section
open ComplexConjugate

/-- `Exp₀` commutes with the involution.  In coordinates the involution
swaps `a` and `b`; the values are real, so complex conjugation fixes
them, and `a + b` is symmetric. -/
theorem Exp0_swap (x : ℚ × ℚ) : Exp0 (x.2, x.1) = Exp0 x := by
  simp only [Exp0]
  ring_nf
end

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution (x : ℚ × ℚ) :
    ((Exp0 (x.2, x.1) : ℂ)) = (starRingEnd ℂ) ((Exp0 x : ℂ)) := by
  rw [Exp0_swap]
  simp [Complex.conj_ofReal]
end
