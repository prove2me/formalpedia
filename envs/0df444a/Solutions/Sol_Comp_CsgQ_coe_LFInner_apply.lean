-- Prove2me | solution 1 for Comp.CsgQ.coe_LFInner_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:33:20.052924+00:00
-- url     : https://prove2.me/submissions/155520f5-6a87-4a2e-b20f-aa734c5cc568

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Theorems.Thm_Comp_CsgQ_coe_lpre1F

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y x : Finset S)
    (w : S → Finset A1) (hw : ∀ s, (G.toCSG h).LW ↑x ↑y s = (↑(w s) : Set A1)) :
    (G.toCSG h).LFInner ↑b ↑y ↑x = (↑(G.lpre1F w x ∪ b) : Set S) := by
  change (G.toCSG h).Lpre1 (↑x : Set S) ↑y ∪ ↑b = (↑(G.lpre1F w x ∪ b) : Set S)
  rw [← coe_lpre1F G h w x y hw, ← Finset.coe_union]
end Comp.CsgQ
