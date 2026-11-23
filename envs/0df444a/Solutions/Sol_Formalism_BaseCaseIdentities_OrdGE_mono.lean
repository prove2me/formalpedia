-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:42.9583+00:00
-- url     : https://prove2.me/submissions/c6be6402-4ae9-4ac4-a32b-a046085369df

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
theorem _root_.solution {a b : ℕ} {f : MvPowerSeries Z k} (h : a ≤ b) (hf : OrdGE b f) : OrdGE a f := by
  intro A hA
  exact hf A (lt_of_lt_of_le hA h)
end OrdGE
end Formalism.BaseCaseIdentities
