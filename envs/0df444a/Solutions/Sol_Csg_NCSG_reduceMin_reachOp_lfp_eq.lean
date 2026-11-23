-- Prove2me | solution 1 for Csg.NCSG.reduceMin_reachOp_lfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:50.053777+00:00
-- url     : https://prove2.me/submissions/3cf751f1-e2a4-418e-b6c6-ea34f1fc8654

import Definitions.Def_Csg_CoalitionComplement
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_CoalitionComplementReach
import Theorems.Thm_Csg_NCSG_reduceMin_reachOp_eq
import Theorems.Thm_Csg_NCSG_reduceMax_r_zero
import Theorems.Thm_Csg_NCSG_reduceMin_r_zero


set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players) (G : NCSG S Players A)
namespace Csg.NCSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) :
    ((G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr)).lfp =
      ((G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr)).lfp :=
  congrArg (fun f => f.lfp) (reduceMin_reachOp_eq C G goal hr)
end Csg.NCSG
