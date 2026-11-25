-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWtG.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:01:48.49642+00:00
-- url     : https://prove2.me/submissions/12dc07f9-acb8-48da-a112-5571564c64bf

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_one
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_one
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
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
variable {k : Type*} [Field k] {S : Type*} {v : AddValuation k (WithTop ℝ)}
namespace Formalism.BaseCaseIdentities
namespace HasWtG
theorem _root_.solution {ω : (S →₀ ℕ) →+ ℝ} {w : ℝ} {f : MvPowerSeries S k}
    (hf : HasWtG v ω w f) (n : ℕ) : HasWtG v ω ((n : ℝ) * w) (f ^ n) := by
  induction n with
  | zero => simpa using (HasWtG.one : HasWtG v ω 0 (1 : MvPowerSeries S k))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring
end HasWtG
end Formalism.BaseCaseIdentities
