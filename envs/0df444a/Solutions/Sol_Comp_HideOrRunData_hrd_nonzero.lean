-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:17:55.90128+00:00
-- url     : https://prove2.me/submissions/e9d1a824-8268-48d4-8f6f-89a59762a910

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution : hrd.Nonzero := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
end Comp.HideOrRunData
