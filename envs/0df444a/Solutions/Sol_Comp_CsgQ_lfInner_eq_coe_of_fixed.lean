-- Prove2me | solution 1 for Comp.CsgQ.lfInner_eq_coe_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:45:44.920128+00:00
-- url     : https://prove2.me/submissions/c0e52684-4c98-4a8a-a3c0-3a4c56f30dfd

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Theorems.Thm_Comp_CsgQ_coe_LFInner_apply
import Theorems.Thm_OrderHom_eq_lfp_of_fixed_of_le


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑c ↑y s = (↑(w s) : Set A1))
    (hfix : c = G.lpre1F w c ∪ b)
    (hle : (↑c : Set S) ≤ ((G.toCSG h).LFInner ↑b ↑y).lfp) :
    ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S) := by
  have hfixS : (G.toCSG h).LFInner (↑b : Set S) ↑y ↑c = (↑c : Set S) := by
    rw [coe_LFInner_apply G h b y c w hw, ← hfix]
  exact (OrderHom.eq_lfp_of_fixed_of_le _ hfixS hle).symm
end Comp.CsgQ
