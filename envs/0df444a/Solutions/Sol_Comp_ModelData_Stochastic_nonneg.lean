-- Prove2me | solution 1 for Comp.ModelData.Stochastic.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:38:51.873404+00:00
-- url     : https://prove2.me/submissions/3af92201-d8bf-4496-b2fb-a27786ff5a98

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData.Stochastic
theorem _root_.solution {d : ModelData} (h : d.Stochastic) : d.Nonneg :=
  fun s t ht => (h s t ht).1
end ModelData.Stochastic
end Comp
