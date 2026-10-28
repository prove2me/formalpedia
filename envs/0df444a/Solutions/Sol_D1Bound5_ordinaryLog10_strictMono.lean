-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:25:33.20357+00:00
-- url     : https://prove2.me/submissions/15c24688-c6b5-4e49-8782-f9b41094f4b2

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_base_pos

section
namespace D1Bound5











theorem _root_.solution {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ordinaryLog10 x < ordinaryLog10 y :=
  div_lt_div_of_pos_right (Real.log_lt_log hx hxy) ordinaryLog10_base_pos











end D1Bound5
end
