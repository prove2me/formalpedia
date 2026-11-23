-- Prove2me | solution 1 for Comp.CsgQ.coe_iter_le_afInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:09:07.572894+00:00
-- url     : https://prove2.me/submissions/f512d5df-d3f9-43f3-9f14-87675f7adc91

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_Comp_CsgQ_coe_AFInner_apply
import Theorems.Thm_Comp_CsgQ_le_lfp_of_step
import Theorems.Thm_OrderHom_le_lfp_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S) (m : ℕ) :
    (↑((G.afStepF b y)^[m] ∅) : Set S) ≤ ((G.toCSG h).AFInner ↑b ↑y).lfp := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact OrderHom.le_lfp_of_step _ ih (coe_AFInner_apply G h b y _).symm
end Comp.CsgQ
