-- Prove2me | solution 1 for Formalism.HC.HostRaw.exists_primitiveRoot_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:56.04914+00:00
-- url     : https://prove2.me/submissions/05a65848-c010-4d6c-809c-4fd8f09a58f8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : ∃ ζ : H.E, IsPrimitiveRoot ζ H.w := UpperTheory.exists_primitiveRoot_torsionOrder H.E
end Formalism.HC.HostRaw
