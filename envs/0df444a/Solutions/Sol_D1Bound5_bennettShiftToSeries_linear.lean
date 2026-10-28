-- Prove2me | solution 1 for D1Bound5.bennettShiftToSeries_linear
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:54.063994+00:00
-- url     : https://prove2.me/submissions/1f9bcf18-c15d-4e07-b2b9-0c3b91ad042b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettLocalResidues_Definitions

section
open Finset

namespace D1Bound5

section Field

variable {F ι : Type*} [Field F] [CharZero F]
variable [Fintype ι] [DecidableEq ι]





@[simp] theorem _root_.solution (b c : F) :
    bennettShiftToSeries b (Polynomial.X - Polynomial.C c) =
      PowerSeries.C (b - c) + PowerSeries.X := by
  change Polynomial.eval₂ PowerSeries.C (PowerSeries.C b + PowerSeries.X)
    (Polynomial.X - Polynomial.C c) = _
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_sub]
  ring

















end Field

end D1Bound5
end
