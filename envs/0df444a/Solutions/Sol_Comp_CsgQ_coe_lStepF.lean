-- Prove2me | solution 1 for Comp.CsgQ.coe_lStepF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:10:33.713205+00:00
-- url     : https://prove2.me/submissions/4e841702-f6b9-4a7e-baec-fe6f4336dbe3

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
import Theorems.Thm_Comp_CsgQ_coe_aF
import Theorems.Thm_Comp_CsgQ_coe_bF

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S)
    (w : Finset A1) :
    (↑(G.lStepF x y s w) : Set A1) = (G.toCSG h).LStep ↑x ↑y s ↑w := by
  change (↑(G.aF (G.bF w x s) y s) : Set A1)
    = (G.toCSG h).A ((G.toCSG h).B ↑w ↑x s) ↑y s
  rw [← coe_bF G h w x s, coe_aF G h]
end Comp.CsgQ
