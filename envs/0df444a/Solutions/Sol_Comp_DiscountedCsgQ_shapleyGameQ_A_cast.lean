-- Prove2me | solution 1 for Comp.DiscountedCsgQ.shapleyGameQ_A_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:43:59.753588+00:00
-- url     : https://prove2.me/submissions/1ba13792-c107-451e-a153-9ca0fa98dbf0

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
import Theorems.Thm_Comp_CsgQ_expect_toCSG


set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ)
    (a1 : A1) (a2 : A2) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).A a1 a2
      = ((G.shapleyGameQ s v).toMatrixGame).A a1 a2 := by
  change ((G.toCsgQ.r s a1 a2 : ℚ) : ℝ)
      + ((G.l : ℚ) : ℝ)
        * (G.toCsgQ.toCSG h.1).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
      = ((G.toCsgQ.r s a1 a2 + G.l * G.toCsgQ.expectQ s a1 a2 v : ℚ) : ℝ)
  rw [CsgQ.expect_toCSG]
  push_cast
  ring
end Comp.DiscountedCsgQ
