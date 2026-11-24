-- Prove2me | solution 1 for Formalism.HC.Der.gal_mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:09.861045+00:00
-- url     : https://prove2.me/submissions/952e5aec-961b-4457-8e81-70a7918011f0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_sqd_ne_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
import Theorems.Thm_Formalism_HC_HostAx_sqd_ne_zero
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
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.mem_Psi_iff, H.gal_sqd σ]
  rcases Int.units_eq_one_or (H.gal σ).1.2 with h | h
  · simp [h]
  · rw [h]
    refine iff_of_false (by decide) fun h1 => sqd_ne_zero H ?_
    have h2 : (2 : H.E) * H.sqd = 0 := by
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
      linear_combination -h1
    simpa using h2
end Formalism.HC.Der
