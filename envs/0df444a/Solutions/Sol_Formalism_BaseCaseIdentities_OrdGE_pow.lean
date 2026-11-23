-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:59.309968+00:00
-- url     : https://prove2.me/submissions/58c29b02-639c-40fa-adde-759e727c8987

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul

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
theorem _root_.solution {f : MvPowerSeries Z k} (hf : OrdGE 1 f) (n : ℕ) : OrdGE n (f ^ n) := by
  induction n with
  | zero => intro A hA; exact absurd hA (Nat.not_lt_zero _)
  | succ n ih => rw [pow_succ]; exact ih.mul hf
end OrdGE
end Formalism.BaseCaseIdentities
