-- Prove2me | solution 1 for Comp.DiscountedCsgQ.toDiscountedCSG_toCSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:47.99471+00:00
-- url     : https://prove2.me/submissions/35aea3f4-2836-4546-bf89-bf2f538c8dbc

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
    (G.toDiscountedCSG h).toCSG = G.toCsgQ.toCSG h.1 := rfl
end Comp.DiscountedCsgQ
