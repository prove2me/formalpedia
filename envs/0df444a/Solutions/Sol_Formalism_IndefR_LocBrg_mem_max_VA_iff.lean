-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.mem_max_VA_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:20.790821+00:00
-- url     : https://prove2.me/submissions/57ade670-d550-471b-90f7-b875350a4510

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
theorem _root_.solution (a : VA L) : a ∈ IsLocalRing.maximalIdeal (VA L) ↔ Valued.v (a : L) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_VA_iff]
  exact ⟨fun h => lt_of_le_of_ne (mem_VA.1 a.2) h, fun h => ne_of_lt h⟩
end Formalism.IndefR.LocBrg
