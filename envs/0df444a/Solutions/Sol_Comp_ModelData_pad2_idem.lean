-- Prove2me | solution 1 for Comp.ModelData.pad2_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:50:21.165812+00:00
-- url     : https://prove2.me/submissions/771aacb1-2fbf-4575-a10a-c990e6ec82fd

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad2_eq_self

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (s a2 : ℕ) : d.pad2 s (d.pad2 s a2) = d.pad2 s a2 :=
  d.pad2_eq_self (d.pad2_mem_keys2 s a2)
end ModelData
end Comp
