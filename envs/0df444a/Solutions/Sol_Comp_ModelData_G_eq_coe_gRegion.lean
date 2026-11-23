-- Prove2me | solution 1 for Comp.ModelData.G_eq_coe_gRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:28:12.553071+00:00
-- url     : https://prove2.me/submissions/74bbf73b-f020-4ec2-b19c-65312f912f07

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_coe_gStepOf
import Theorems.Thm_Comp_ModelData_wellFormed
import Theorems.Thm_Comp_gfp_eq_coe_fixFrom_univ


set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (h2 : d.Stochastic)
    (hnz : d.Nonzero) (safe : Finset (Fin d.nStates)) :
    (d.toCsgQ.toCSG (d.wellFormed hs h2)).G (↑safe : Set (Fin d.nStates))
      = (↑(d.gRegion hs safe) : Set (Fin d.nStates)) :=
  gfp_eq_coe_fixFrom_univ _ _ (d.coe_gStepOf hs h2 hnz safe)
end Comp.ModelData
