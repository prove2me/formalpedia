-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_mul
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:52.059557+00:00
-- url     : https://prove2.me/submissions/205c8bef-71b0-4b5e-aca5-542c62768a9c

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5





theorem _root_.solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordinaryLog10 (x*y) = ordinaryLog10 x+ordinaryLog10 y := by
  simp only [ordinaryLog10,Real.log_mul hx hy]
  ring

















end D1Bound5
end
