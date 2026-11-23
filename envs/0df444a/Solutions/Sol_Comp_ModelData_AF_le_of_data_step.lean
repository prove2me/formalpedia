-- Prove2me | solution 1 for Comp.ModelData.AF_le_of_data_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:15.511797+00:00
-- url     : https://prove2.me/submissions/93118a44-f409-4d59-975d-5be6facd62ad

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_afInner_eq_of_data
import Theorems.Thm_Comp_CsgQ_AF_le_of_step
import Theorems.Thm_Comp_ModelData_wellFormed


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (b y c : Finset (Fin d.nStates)) (m : ℕ)
    (hiter : (d.afStepOf hs b y)^[m] ∅ = c) (hfix : d.afStepOf hs b y c = c)
    (hy : (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑y : Set (Fin d.nStates))) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).AF ↑b ≤ (↑c : Set (Fin d.nStates)) :=
  CsgQ.AF_le_of_step d.toCsgQ (d.wellFormed hs h2) b y c
    (d.afInner_eq_of_data hs h2 hnz b y c m hiter hfix) hy
end Comp.ModelData
