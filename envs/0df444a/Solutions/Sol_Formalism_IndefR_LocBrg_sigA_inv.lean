-- Prove2me | solution 1 for Formalism.IndefR.LocBrg.sigA_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.324149+00:00
-- url     : https://prove2.me/submissions/731706e6-3f8e-48bb-a7c1-61da1491c70a

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
variable (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
namespace Formalism.IndefR.LocBrg
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (x : VA L) : sigA σ hv (sigA σ hv x) = x := by
  apply Subtype.ext
  exact hσ x
end Formalism.IndefR.LocBrg
