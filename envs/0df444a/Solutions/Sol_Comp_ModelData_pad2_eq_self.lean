-- Prove2me | solution 1 for Comp.ModelData.pad2_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:47:27.23568+00:00
-- url     : https://prove2.me/submissions/a5f526e9-654e-4e03-8d7e-71a42a6cdde1

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) {s a2 : ℕ} (h : a2 ∈ d.keys2 s) :
    d.pad2 s a2 = a2 := by
  unfold ModelData.pad2
  split_ifs
  rfl
end ModelData
end Comp
