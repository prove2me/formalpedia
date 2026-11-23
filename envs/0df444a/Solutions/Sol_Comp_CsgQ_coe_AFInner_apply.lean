-- Prove2me | solution 1 for Comp.CsgQ.coe_AFInner_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:05:50.772916+00:00
-- url     : https://prove2.me/submissions/fa450927-c7ad-49cd-9145-349edd6672f3

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_Comp_CsgQ_coe_apre1F

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S) :
    (G.toCSG h).AFInner ↑b ↑y ↑x = (↑(G.afStepF b y x) : Set S) := by
  change (G.toCSG h).Apre1 (↑x : Set S) ↑y ∪ ↑b = (↑(G.apre1F x y ∪ b) : Set S)
  rw [← coe_apre1F G h x y, ← Finset.coe_union]
end Comp.CsgQ
