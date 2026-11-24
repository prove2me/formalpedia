-- Prove2me | solution 1 for Formalism.HC.Der.mem_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:08.81156+00:00
-- url     : https://prove2.me/submissions/0709a125-ee4d-4a91-9526-889eefd60b0e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_conj_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : ∀ x : H.E, x ∈ H.F ↔ H.conj x = x := by
  intro x
  rw [mem_maximalRealSubfield_iff]
  constructor
  · intro hx
    let ψ : H.E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply ψ.injective
    rw [conj_apply]
    exact hx ψ
  · intro hx ψ
    have := conj_apply H ψ x
    rw [hx] at this
    exact this.symm
end Formalism.HC.Der
