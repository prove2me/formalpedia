-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:45.193514+00:00
-- url     : https://prove2.me/submissions/15eaa148-4ad2-4853-a7a1-8da088ed6d36

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
theorem _root_.solution {n : ℕ} {f : MvPowerSeries Z k} (hf : OrdGE n f) : OrdGE n (-f) := by
  intro A hA
  rw [map_neg, hf A hA, neg_zero]
end OrdGE
end Formalism.BaseCaseIdentities
