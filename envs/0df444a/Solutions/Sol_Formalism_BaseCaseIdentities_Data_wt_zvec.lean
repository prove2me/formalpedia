-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_zvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:51.845744+00:00
-- url     : https://prove2.me/submissions/2354e62e-9b16-44fe-ba0e-f4fdaec7c189

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero


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
variable {k : Type*} [Field k] {Z C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (c : C) : D.Wt D.rad (D.zvec c) := by
  unfold zvec
  apply HasWt.sum
  intro d _
  split_ifs
  · exact HasWt.X d
  · exact HasWt.zero
end Formalism.BaseCaseIdentities.Data
