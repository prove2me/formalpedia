-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.noConst_fixPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:15.70029+00:00
-- url     : https://prove2.me/submissions/f8be3f7d-956b-4db0-89e9-4c0737f8077f

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zero

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
theorem _root_.solution : NoConst D.fixPt := by
  intro c A hA
  exact D.noConst_iterate noConst_zero A.degree c A hA
end Formalism.BaseCaseIdentities.Data
