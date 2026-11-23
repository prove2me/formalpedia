-- Prove2me | solution 1 for Csg.NCSG.reduceMin_reachOp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:50.938245+00:00
-- url     : https://prove2.me/submissions/3e13c043-523e-435f-87c3-8a10af72f4c5

import Definitions.Def_Csg_CoalitionComplement
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_CoalitionComplementReach
import Theorems.Thm_Csg_NCSG_reduceMin_reachOpFun_eq
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
    (G.reduceMax Cᶜ).reachOp goal (G.reduceMax_r_zero Cᶜ hr) =
      (G.reduceMin C).reachOp goal (G.reduceMin_r_zero C hr) := by
  apply OrderHom.ext
  funext v s
  exact reduceMin_reachOpFun_eq C G goal hr v s
end Csg.NCSG
