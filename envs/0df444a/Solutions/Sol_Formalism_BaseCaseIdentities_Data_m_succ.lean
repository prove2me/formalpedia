-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.m_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:02.645803+00:00
-- url     : https://prove2.me/submissions/1caf8ec1-aefb-4aac-8a66-41f6f34319ca

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
theorem _root_.solution (s : ℕ) (b : C) : D.m (s + 1) b = MvPowerSeries.C (-(D.l : k)⁻¹) *
    ∑ c, frob D.q (D.m s c) * MvPowerSeries.C (D.g c b) := rfl
end Formalism.BaseCaseIdentities.Data
