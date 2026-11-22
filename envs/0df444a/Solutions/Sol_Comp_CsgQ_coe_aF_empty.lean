-- Prove2me | solution 1 for Comp.CsgQ.coe_aF_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:42.747886+00:00
-- url     : https://prove2.me/submissions/05749d65-c4f6-4290-baf7-b22a9fb5c4c5

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_Comp_CsgQ_coe_aF


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (y : Finset S) (s : S) :
    (↑(G.aF ∅ y s) : Set A1) = (G.toCSG h).A ∅ ↑y s := by
  rw [coe_aF G h ∅ y s, Finset.coe_empty]
end Comp.CsgQ
