-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGen.incl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:03:27.499971+00:00
-- url     : https://prove2.me/submissions/75a53553-688c-467c-877c-a2c40d47b1a8

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLatticeOfRel
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGen
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLevelIdx
open scoped ENNReal TensorProduct
namespace Formalism.MainNotions.BridgeLevelGen
theorem _root_.solution (I : AutInst) (b : 𝓞 I.E) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E b) ∈ IntAf I.F I.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, ⟨b, rfl⟩⟩, rfl⟩)
end Formalism.MainNotions.BridgeLevelGen
