-- Prove2me | solution 1 for Formalism.HC.HostAx.galE_mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:20.05636+00:00
-- url     : https://prove2.me/submissions/e81f7339-3d26-4c70-841c-ad3048241ed5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Theorems.Thm_Formalism_HC_HostAx_galE_bE
import Theorems.Thm_Formalism_HC_HostAx_sqd_ne_zero
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
attribute [instance] HostRaw.instField HostRaw.instNF
open Formalism.HC.HostAx
variable {φ : Frame} (H : HostAx φ)
namespace Formalism.HC.HostAx
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) : H.galE σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  have hs := H.sqd_ne_zero
  rw [H.galE_bE σ]
  change (H.galE σ).1.2 = 1 ↔ _
  rcases Int.units_eq_one_or (H.galE σ).1.2 with h | h <;> rw [h]
  · simp
  · constructor
    · intro h2
      exact absurd h2 (by decide)
    · intro h2
      exfalso
      apply hs
      have h4 : ((((-1 : ℤˣ) : ℤ) : H.E)) = -1 := by simp
      rw [h4] at h2
      have h3 : (2 : H.E) * H.sqd = 0 := by linear_combination -h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
end Formalism.HC.HostAx
