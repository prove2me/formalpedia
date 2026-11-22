-- Prove2me | solution 1 for Comp.CsgQ.expect_toCSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:38:53.156278+00:00
-- url     : https://prove2.me/submissions/d9871e87-8b34-45ec-b87b-cf87187507cb

import Definitions.Def_Csg_Discounted
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Comp_Basic
import Theorems.Thm_Comp_CsgQ_toPMF_toReal

set_option autoImplicit true
open Comp
open Csg
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
open Comp.CsgQ
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2)
    (v : S → ℚ) :
    (G.toCSG h).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
      = ((G.expectQ s a1 a2 v : ℚ) : ℝ) := by
  unfold CSG.expect expectQ
  push_cast
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [show (G.toCSG h).K s a1 a2 s' = G.toPMF h s a1 a2 s' from rfl, toPMF_toReal]
end Comp.CsgQ
