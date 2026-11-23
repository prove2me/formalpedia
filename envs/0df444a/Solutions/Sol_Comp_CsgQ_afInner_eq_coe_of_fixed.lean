-- Prove2me | solution 1 for Comp.CsgQ.afInner_eq_coe_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:13:19.392924+00:00
-- url     : https://prove2.me/submissions/6e99d34b-0e6a-4dc4-a7f5-79f71a8b876b

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_Comp_CsgQ_coe_AFInner_apply
import Theorems.Thm_Comp_CsgQ_coe_iter_le_afInner
import Theorems.Thm_OrderHom_eq_lfp_of_fixed_of_le


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S) (m : ℕ)
    (hiter : (G.afStepF b y)^[m] ∅ = c) (hfix : G.afStepF b y c = c) :
    ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hle := coe_iter_le_afInner G h b y m
  rw [hiter] at hle
  have hfixS : (G.toCSG h).AFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [coe_AFInner_apply G h b y c, hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm
end Comp.CsgQ
