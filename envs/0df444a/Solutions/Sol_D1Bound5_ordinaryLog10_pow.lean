-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_pow
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:32.72451+00:00
-- url     : https://prove2.me/submissions/683417ce-2598-4ff8-8335-25d4fe782ecf

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5







theorem _root_.solution (x : ℝ) (n : ℕ) :
    ordinaryLog10 (x^n) = n*ordinaryLog10 x := by
  simp only [ordinaryLog10,Real.log_pow]
  ring















end D1Bound5
end
