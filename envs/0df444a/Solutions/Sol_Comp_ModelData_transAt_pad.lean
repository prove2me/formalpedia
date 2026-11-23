-- Prove2me | solution 1 for Comp.ModelData.transAt_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:06:31.3578+00:00
-- url     : https://prove2.me/submissions/74497a8f-13bd-4d14-bf05-6f8d0f9267e5

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad1_idem
import Theorems.Thm_Comp_ModelData_pad2_idem

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (s a1 a2 : ℕ) :
    d.transAt s (d.pad1 s a1) (d.pad2 s a2) = d.transAt s a1 a2 := by
  unfold ModelData.transAt
  rw [d.pad1_idem s a1, d.pad2_idem s a2]
end ModelData
end Comp
