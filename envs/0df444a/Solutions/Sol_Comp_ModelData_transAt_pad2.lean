-- Prove2me | solution 1 for Comp.ModelData.transAt_pad2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:11:40.523803+00:00
-- url     : https://prove2.me/submissions/befefe11-47df-4794-8c8a-b685d8e53d6e

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad2_idem

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s a1 (d.pad2 s a2) = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad2_idem s a2]
end ModelData
end Comp
