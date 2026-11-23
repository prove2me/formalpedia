-- Prove2me | solution 1 for Comp.ModelData.coe_LFInner_of_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:45.557537+00:00
-- url     : https://prove2.me/submissions/58fe71aa-6043-4d4e-ab0b-ee232caa05fb

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_lpre1F_eq
import Theorems.Thm_Comp_ModelData_LW_eq_of_data
import Theorems.Thm_Comp_CsgQ_coe_LFInner_apply
import Theorems.Thm_Comp_ModelData_Stochastic_nonneg
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (k : ℕ) (b y x : Finset (Fin d.nStates))
    (hlw : ∀ s, d.lStepOf hs x y s ((d.lStepOf hs x y s)^[k] ∅) = (d.lStepOf hs x y s)^[k] ∅) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).LFInner ↑b ↑y ↑x
      = (↑(d.midOf hs k b y x) : Set (Fin d.nStates)) := by
  rw [CsgQ.coe_LFInner_apply d.toCsgQ (d.wellFormed hs h2) b y x
      (fun s => (d.lStepOf hs x y s)^[k] ∅)
      (fun s => d.LW_eq_of_data hs h2 hnz k x y s (hlw s)),
    d.lpre1F_eq hs h2.nonneg hnz]
  rfl
end Comp.ModelData
