-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.cO_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:19.414707+00:00
-- url     : https://prove2.me/submissions/980caa43-839a-42d9-abab-cf417e161fc2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MemTorsionOfMulConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (y : 𝓞 E) : ((cO E y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := rfl
end Formalism.L2.SG.NGCut.TorsionTotientBound
