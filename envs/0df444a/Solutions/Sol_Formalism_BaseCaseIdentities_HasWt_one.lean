-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:30.341799+00:00
-- url     : https://prove2.me/submissions/3dea6182-42fc-41da-a7a3-6a20aa0c5847

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_IdentityTwentyB
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd

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
variable {k : Type*} [Field k] {Z : Type*} {v : AddValuation k (WithTop ℝ)}
  {r w w' w1 w2 wa wb a₀ : ℝ} {f g a b : MvPowerSeries Z k}
namespace Formalism.BaseCaseIdentities
namespace HasWt
theorem _root_.solution : HasWt v r 0 (1 : MvPowerSeries Z k) := by
  classical
  rw [hasWt_iff]
  intro A
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp
end HasWt
end Formalism.BaseCaseIdentities
