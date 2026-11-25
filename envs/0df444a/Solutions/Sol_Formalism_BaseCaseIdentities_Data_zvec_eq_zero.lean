-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.zvec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:04.916136+00:00
-- url     : https://prove2.me/submissions/3e74ac29-eba7-4deb-9249-b9d7e04d12dc

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI

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
theorem _root_.solution {c : C} (hc : D.lev c ≠ 0) : D.zvec c = 0 := by
  unfold zvec
  apply Finset.sum_eq_zero
  intro d _
  rw [if_neg]
  rintro rfl
  exact hc (D.ι_lev d)
end Formalism.BaseCaseIdentities.Data
