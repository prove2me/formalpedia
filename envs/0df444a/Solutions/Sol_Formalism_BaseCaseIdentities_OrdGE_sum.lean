-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:43.706378+00:00
-- url     : https://prove2.me/submissions/33e754bf-7440-495e-88a9-32d56856e280

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
theorem _root_.solution {ι : Type*} {n : ℕ} (s : Finset ι) {f : ι → MvPowerSeries Z k}
    (hf : ∀ i ∈ s, OrdGE n (f i)) : OrdGE n (∑ i ∈ s, f i) := by
  intro A hA
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi A hA
end OrdGE
end Formalism.BaseCaseIdentities
