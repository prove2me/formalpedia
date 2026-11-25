-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.HasWt.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:33.867652+00:00
-- url     : https://prove2.me/submissions/112f7aa8-6d0b-4151-b7d9-7238b9b95c4e

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {F : ι → MvPowerSeries Z k}
    (h : ∀ i ∈ s, HasWt v r w (F i)) : HasWt v r w (∑ i ∈ s, F i) := by
  rw [hasWt_iff]
  intro A
  rw [map_sum]
  exact v.map_le_sum fun i hi => (hasWt_iff.1 (h i hi)) A
end HasWt
end Formalism.BaseCaseIdentities
