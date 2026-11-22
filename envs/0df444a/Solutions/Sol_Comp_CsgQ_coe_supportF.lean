-- Prove2me | solution 1 for Comp.CsgQ.coe_supportF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:52:57.762196+00:00
-- url     : https://prove2.me/submissions/d6d76bb3-09b2-4648-a741-fedf34fa84d7

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) :
    (↑(G.supportF s a1 a2) : Set S) = G.supportQ s a1 a2 := by
  ext s'
  simp [supportF, supportQ]
end Comp.CsgQ
