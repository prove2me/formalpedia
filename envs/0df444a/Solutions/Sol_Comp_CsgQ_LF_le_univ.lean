-- Prove2me | solution 1 for Comp.CsgQ.LF_le_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:06:59.161947+00:00
-- url     : https://prove2.me/submissions/066872ea-2170-4f31-a824-256b292388b1

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).LF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top
end Comp.CsgQ
