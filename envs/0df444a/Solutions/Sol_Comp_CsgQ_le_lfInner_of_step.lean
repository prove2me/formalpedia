-- Prove2me | solution 1 for Comp.CsgQ.le_lfInner_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:35:22.025811+00:00
-- url     : https://prove2.me/submissions/336e18ba-57d9-432b-962d-c1af08a92876

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Theorems.Thm_Comp_CsgQ_coe_LFInner_apply
import Theorems.Thm_Comp_CsgQ_le_lfp_of_step
import Theorems.Thm_OrderHom_le_lfp_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1))
    (hle : (↑x : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp)
    (hc : c = G.lpre1F w x ∪ b) :
    (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp := by
  subst hc
  exact OrderHom.le_lfp_of_step _ hle (coe_LFInner_apply G h b y x w hw).symm
end Comp.CsgQ
