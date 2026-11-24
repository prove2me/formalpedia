-- Prove2me | solution 1 for Formalism.HC.Der.kc_diff_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:22.258662+00:00
-- url     : https://prove2.me/submissions/93581fd2-b76d-45ad-af30-adef5984d14f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_comm_of
import Theorems.Thm_Formalism_HC_Der_kc_diff_smul_mem
import Theorems.Thm_Formalism_HC_Der_kc_diff_smul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) = differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  apply le_antisymm (kc_diff_smul_le H σ (kc_comm_of H σ))
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact kc_diff_smul_mem H σ⁻¹ (kc_comm_of H σ⁻¹) x hx
end Formalism.HC.Der
