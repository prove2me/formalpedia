-- Prove2me | solution 1 for Formalism.HC.HostRaw.isPrimOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:42.477937+00:00
-- url     : https://prove2.me/submissions/ded8ce4d-4381-47ea-9108-ca1bcc255527

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Theorems.Thm_Formalism_HC_An_Induces_unique
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim

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
theorem _root_.solution (θ : φ.Char) (ψ : PChar) : H.IsPrimOf θ ψ.χ ↔ ψ = H.prim θ := by
  constructor
  · intro h
    have hN : H.condN ≠ 0 := NeZero.ne _
    exact An.Induces.unique hN h (H.isPrimOf_prim θ)
  · rintro rfl
    exact H.isPrimOf_prim θ
end Formalism.HC.HostRaw
