-- Prove2me | solution 1 for Formalism.HC.HostRaw.dir_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:31.641885+00:00
-- url     : https://prove2.me/submissions/c88c9391-1e5a-4a67-a711-fa931d1b01ca

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic

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
theorem _root_.solution (θ : φ.Char) (u : (ZMod H.condN)ˣ) : H.dir θ u = θ (H.art u) := by
  rw [dir, MulChar.ofUnitHom_coe]
  rfl
end Formalism.HC.HostRaw
