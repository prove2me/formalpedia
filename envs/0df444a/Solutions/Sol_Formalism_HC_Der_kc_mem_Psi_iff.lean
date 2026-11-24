-- Prove2me | solution 1 for Formalism.HC.Der.kc_mem_Psi_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:15.38292+00:00
-- url     : https://prove2.me/submissions/3556b2e7-688b-4ea8-a628-deff4f460153

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_sqd_ne_zero
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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) : H.gal σ ∈ φ.Psi ↔ σ H.sqd = H.sqd := by
  rw [Frame.Psi, MonoidHom.mem_ker, H.gal_sqd]
  simp only [Frame.chD, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd]
  rcases Int.units_eq_one_or ((H.gal σ).1.2) with h | h <;> rw [h]
  · simp
  · constructor
    · intro h1
      exact absurd h1 (by decide)
    · intro h1
      exfalso
      have h2 : (2 : H.E) * H.sqd = 0 := by
        push_cast at h1
        linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact kc_sqd_ne_zero H h3
end Formalism.HC.Der
