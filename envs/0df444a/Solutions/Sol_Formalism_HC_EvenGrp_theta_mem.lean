-- Prove2me | solution 1 for Formalism.HC.EvenGrp.theta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:16:12.825077+00:00
-- url     : https://prove2.me/submissions/24be5d6a-b9fb-40a6-ae94-585f61eccf6f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_EvenData_mem_cusp_forms_iff_automorphic_compact
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Frame_mem_cusp_forms_iff_automorphic_compact
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
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
namespace Formalism.HC.EvenGrp
theorem _root_.solution (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) : theta Ξ e hev χ hχ ∈ (frame Ξ e hev).Chat := by
  simp only [Frame.Chat, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · unfold Frame.TrivialOnFirstFactor
    intro s hs
    have h1 := ((data Ξ e hev).mem_cusp_forms_iff_automorphic_compact s).mp hs
    show thetaB Ξ χ hχ ((data Ξ e hev).xiA ((data Ξ e hev).frame.iota s)) = 1
    rw [h1]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)
  · show thetaB Ξ χ hχ ((data Ξ e hev).xiA 1) = 1
    rw [map_one]
    exact map_one (thetaB Ξ χ hχ)
end Formalism.HC.EvenGrp
