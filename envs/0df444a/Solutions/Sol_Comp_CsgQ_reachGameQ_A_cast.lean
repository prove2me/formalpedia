-- Prove2me | solution 1 for Comp.CsgQ.reachGameQ_A_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:26:28.45581+00:00
-- url     : https://prove2.me/submissions/b8d5b753-760d-4ca0-aff0-d66c08b62d0e

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_expect_toCSG


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) (a1 : A1) (a2 : A2) :
    ((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).A a1 a2
      = ((G.reachGameQ s v).toMatrixGame).A a1 a2 := by
  change (G.toCSG h).r s a1 a2
      + (G.toCSG h).expect s a1 a2 (fun s' => ((v s' : ℚ) : ℝ))
    = ((G.expectQ s a1 a2 v : ℚ) : ℝ)
  rw [toCSG_r_zero G h hr0 s a1 a2, CsgQ.expect_toCSG, zero_add]
end Comp.CsgQ
