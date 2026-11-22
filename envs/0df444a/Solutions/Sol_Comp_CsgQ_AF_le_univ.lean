-- Prove2me | solution 1 for Comp.CsgQ.AF_le_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:00:14.449498+00:00
-- url     : https://prove2.me/submissions/afe3f24c-65ef-4268-83ae-2e4ad456bcaf

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b : Finset S) :
    (G.toCSG h).AF ↑b ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top
end Comp.CsgQ
