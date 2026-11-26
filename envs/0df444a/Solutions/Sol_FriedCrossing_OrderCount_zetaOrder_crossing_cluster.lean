-- Prove2me | solution 1 for FriedCrossing.OrderCount.zetaOrder_crossing_cluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:32.763888+00:00
-- url     : https://prove2.me/submissions/b172150a-6a71-4ce8-8ca3-94ecc1522615

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
theorem _root_.solution : zetaOrder ![0, 1, 2, 1, 0] = 0 := by decide
end FriedCrossing.OrderCount
