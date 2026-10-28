-- Prove2me | solution 1 for D1Bound5.ordinaryLog10_ten
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:30:15.938993+00:00
-- url     : https://prove2.me/submissions/d9d17e6c-87f5-4c16-ad0d-2e50ae2a0744

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Theorems.Thm_D1Bound5_ordinaryLog10_base_pos

section
namespace D1Bound5









theorem _root_.solution : ordinaryLog10 10 = 1 := by
  exact div_self ordinaryLog10_base_pos.ne'













end D1Bound5
end
