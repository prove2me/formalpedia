-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.OrdGE.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:44.182541+00:00
-- url     : https://prove2.me/submissions/53a73412-2c2b-422d-a744-b99abd0470a5

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
theorem _root_.solution {n : ℕ} {f g : MvPowerSeries Z k} (hf : OrdGE n f) (hg : OrdGE n g) :
    OrdGE n (f + g) := by
  intro A hA
  rw [map_add, hf A hA, hg A hA, add_zero]
end OrdGE
end Formalism.BaseCaseIdentities
