-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.noConst_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.303869+00:00
-- url     : https://prove2.me/submissions/c275cf14-cb70-4069-93fe-646ccf1c661b

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_Psi

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
theorem _root_.solution {t : C → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst ((D.Psi)^[n] t) := by
  cases n with
  | zero => exact ht
  | succ n => rw [Function.iterate_succ_apply']; exact D.noConst_Psi _
end Formalism.BaseCaseIdentities.Data
