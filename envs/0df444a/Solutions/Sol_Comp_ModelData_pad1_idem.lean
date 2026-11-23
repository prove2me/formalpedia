-- Prove2me | solution 1 for Comp.ModelData.pad1_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:49:29.004666+00:00
-- url     : https://prove2.me/submissions/c2045188-5bc2-4a61-9bd5-d4adeb7c4e2b

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad1_eq_self

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (s a1 : ℕ) : d.pad1 s (d.pad1 s a1) = d.pad1 s a1 :=
  d.pad1_eq_self (d.pad1_mem_keys1 s a1)
end ModelData
end Comp
