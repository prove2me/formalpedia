-- Prove2me | solution 1 for Formalism.HC.HostRaw.kept_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:18.131244+00:00
-- url     : https://prove2.me/submissions/99025330-57ec-4e96-9066-9eda5b462eeb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff

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
theorem _root_.solution (S : Finset PChar) (θ : φ.Char) : H.Kept S θ ↔ H.prim θ ∈ S := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    rwa [(H.isPrimOf_iff θ ψ).mp h] at hψ
  · intro h
    exact ⟨H.prim θ, h, H.isPrimOf_prim θ⟩
end Formalism.HC.HostRaw
