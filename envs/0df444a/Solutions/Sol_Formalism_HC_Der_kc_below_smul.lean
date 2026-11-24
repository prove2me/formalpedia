-- Prove2me | solution 1 for Formalism.HC.Der.kc_below_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:06.768236+00:00
-- url     : https://prove2.me/submissions/030e9c51-062f-4e86-9e68-679168f834ff

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiff
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_kc_fixK
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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (P : Ideal (𝓞 H.E)) :
    kcBelow H (σ • P) = kcBelow H P := by
  ext a
  simp only [kcBelow, Ideal.mem_comap]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hσ' : H.gal σ⁻¹ ∈ φ.Psi := by
    rw [map_inv]
    exact inv_mem hσ
  have e : σ⁻¹ • algebraMap (𝓞 H.K) (𝓞 H.E) a = algebraMap (𝓞 H.K) (𝓞 H.E) a := by
    apply NumberField.RingOfIntegers.ext
    show σ⁻¹ ((a : H.K) : H.E) = ((a : H.K) : H.E)
    exact kc_fixK H σ⁻¹ hσ' (a : H.K)
  rw [e]
end Formalism.HC.Der
