-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.mem_intL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.372865+00:00
-- url     : https://prove2.me/submissions/2bd9309c-8b07-4f5e-acab-e12e51e6d26f

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_WittDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_FinNormSurj
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LocalNormSurjectivity_MemMaxVAIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.IndefR Formalism.IndefR.LocBrg
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.IndefR.LocBrg
theorem _root_.solution {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Valuation.mem_integer_iff _ _
end Formalism.IndefR.LocBrg
