-- Prove2me | solution 1 for Comp.CsgQ.le_lfp_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:58:49.214596+00:00
-- url     : https://prove2.me/submissions/600927e0-aea2-4af0-961d-244b225be334

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_reachOp_castIcc_eq
import Theorems.Thm_OrderHom_le_lfp_of_step


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
    (hv : castIcc v h0 h1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp)
    (hstep : ∀ s, ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((w s : ℚ) : ℝ)) :
    castIcc w k0 k1 ≤ ((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)).lfp :=
  OrderHom.le_lfp_of_step _ hv
    (reachOp_castIcc_eq G h hr0 goal v w h0 h1 k0 k1 hstep).symm
end Comp.CsgQ
