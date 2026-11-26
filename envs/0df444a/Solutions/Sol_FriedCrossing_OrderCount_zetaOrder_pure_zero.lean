-- Prove2me | solution 1 for FriedCrossing.OrderCount.zetaOrder_pure_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:29.734361+00:00
-- url     : https://prove2.me/submissions/ba9cb1ba-fd3e-4f0b-b33a-a619afc4e044

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.OrderCount
variable {K : Type*} [Field K] {V₁ V₂ V₃ : Type*}
  [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
  [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
  [AddCommGroup V₃] [Module K V₃]
namespace FriedCrossing.OrderCount
theorem _root_.solution : zetaOrder ![0, 0, 1, 0, 0] = 1 := by decide
end FriedCrossing.OrderCount
