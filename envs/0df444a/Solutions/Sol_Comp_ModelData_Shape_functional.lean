-- Prove2me | solution 1 for Comp.ModelData.Shape.functional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:34.221891+00:00
-- url     : https://prove2.me/submissions/7ff68943-6dc0-40ec-ac15-bbc12c2f3c22

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData.Shape
theorem _root_.solution {d : ModelData} (hs : d.Shape) : d.Functional := hs.2.2.1
end ModelData.Shape
end Comp
