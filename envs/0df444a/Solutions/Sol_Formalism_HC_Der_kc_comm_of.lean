-- Prove2me | solution 1 for Formalism.HC.Der.kc_comm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:49.17724+00:00
-- url     : https://prove2.me/submissions/8a4d2d45-6783-47a0-b6fc-cfa4456992b8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ (τ x) = τ (σ x) := by
  have h : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ :=
    H.gal.injective (by rw [map_mul, map_mul, mul_comm])
  have := congrArg (fun f : H.E ≃ₐ[ℚ] H.E => f x) h
  simpa only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply] using this
end Formalism.HC.Der
