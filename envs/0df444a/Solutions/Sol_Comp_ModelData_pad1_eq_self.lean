-- Prove2me | solution 1 for Comp.ModelData.pad1_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:47:03.773631+00:00
-- url     : https://prove2.me/submissions/839cca05-e53a-476d-84cd-279bd750dc0a

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) {s a1 : ℕ} (h : a1 ∈ d.keys1 s) :
    d.pad1 s a1 = a1 := by
  unfold ModelData.pad1
  split_ifs
  rfl
end ModelData
end Comp
