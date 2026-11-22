-- Prove2me | solution 1 for Comp.CsgQ.reachOp_castIcc_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:45.024634+00:00
-- url     : https://prove2.me/submissions/9bcb0565-cab1-4225-9829-d575493bfaa8

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


attribute [local simp] Comp.CsgQ.castIcc_coe

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v w : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1)
    (k0 : ∀ s, 0 ≤ w s) (k1 : ∀ s, w s ≤ 1)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) = castIcc w k0 k1 := by
  funext s
  exact Subtype.ext (hstep s)
end Comp.CsgQ
