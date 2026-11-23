-- Prove2me | solution 1 for Formalism.HC.HostRaw.isPrimOf_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:01.57527+00:00
-- url     : https://prove2.me/submissions/c87e397a-cb09-4674-95ee-7abac6d9188c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Theorems.Thm_Formalism_HC_An_induces_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution (θ : φ.Char) : H.IsPrimOf θ (H.prim θ).χ :=
  An.induces_of (H.dir θ)
end Formalism.HC.HostRaw
