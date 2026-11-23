-- Prove2me | solution 1 for Comp.DiscountedCsgQ.toDiscountedCSG_l
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:48.786878+00:00
-- url     : https://prove2.me/submissions/e16a4842-ecc6-4d9c-8e68-2ec0f31b985e

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic

set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.DiscountedCsgQ
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) :
    (G.toDiscountedCSG h).l = ((G.l : ℚ) : ℝ) := rfl
end Comp.DiscountedCsgQ
