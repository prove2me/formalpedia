-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.noConst_zvec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:40.962047+00:00
-- url     : https://prove2.me/submissions/6a44cb91-d90f-4104-9395-53cc5bf7510b

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : NoConst D.zvec := by
  intro b
  refine OrdGE.sum _ fun d _ => ?_
  split_ifs
  · exact OrdGE.X d
  · exact OrdGE.zero
end Formalism.BaseCaseIdentities.Data
