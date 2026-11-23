-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:37:52.65491+00:00
-- url     : https://prove2.me/submissions/c83cd584-0b62-454a-b013-55f3f1f01586

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution : hrd.Nonneg := by
  intro s
  fin_cases s <;>
    norm_num [ModelData.transOf, ModelData.stateAt, or_imp, and_imp, forall_and,
      forall_eq']
end Comp.HideOrRunData
