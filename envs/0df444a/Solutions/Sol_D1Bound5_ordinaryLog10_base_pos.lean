-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_base_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:32.44295+00:00
-- url     : https://prove2.me/submissions/83971a48-903e-4fc3-bf1d-c28b5168cb48

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

section
namespace D1Bound5



theorem _root_.solution : 0 < Real.log (10 : ℝ) :=
  Real.log_pos (by norm_num)



















end D1Bound5
end
