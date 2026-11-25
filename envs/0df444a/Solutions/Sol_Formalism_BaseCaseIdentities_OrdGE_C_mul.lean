-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:27.973803+00:00
-- url     : https://prove2.me/submissions/1e04889f-93b9-40a7-87ab-305f45d0a3ec

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint

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
namespace Formalism.BaseCaseIdentities
namespace OrdGE
theorem _root_.solution {n : ℕ} {f : MvPowerSeries Z k} (x : k) (hf : OrdGE n f) :
    OrdGE n (MvPowerSeries.C x * f) := by
  intro A hA
  rw [coeff_C_mul, hf A hA, mul_zero]
end OrdGE
end Formalism.BaseCaseIdentities
