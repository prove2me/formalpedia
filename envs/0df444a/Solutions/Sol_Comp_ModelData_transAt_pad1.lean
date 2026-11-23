-- Prove2me | solution 1 for Comp.ModelData.transAt_pad1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:10:32.110398+00:00
-- url     : https://prove2.me/submissions/3669b12b-4bca-4319-85e4-ea7174dbb2ea

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad1_idem

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) a2 = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad1_idem s a1]
end ModelData
end Comp
