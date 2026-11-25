-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.weighted_pow_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:32.742702+00:00
-- url     : https://prove2.me/submissions/7ca9b1bb-d370-486c-9c11-c87f89285d0e

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow


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
namespace Formalism.BaseCaseIdentities
theorem _root_.solution (k : Type*) [Field k] (Z : Type*) : PowRule k Z :=
  fun _ _ _ _ N hf => hf.pow N
end Formalism.BaseCaseIdentities
