-- Prove2me | solution 1 for FriedCrossing.OrderCount.zetaOrder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:54:15.639802+00:00
-- url     : https://prove2.me/submissions/f6d0bb2d-0bfc-4d92-a69f-b0108c2186f7

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
theorem _root_.solution (c : Fin 5 → ℕ) (h0 : c 0 = 0) (h4 : c 4 = 0) (h31 : c 3 = c 1) :
    zetaOrder c = (c 2 : ℤ) - 2 * c 1 := by
  simp only [zetaOrder, Fin.sum_univ_five, h0, h4, h31]
  norm_num
  ring
end FriedCrossing.OrderCount
