-- Prove2me | solution 1 for Formalism.HC.Der.kc_diff_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:23.54412+00:00
-- url     : https://prove2.me/submissions/f412a5da-b193-474d-a567-53095a5a0a24

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem
import Theorems.Thm_Formalism_HC_Der_kc_diff_smul_mem

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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 H.K) (𝓞 H.E) ≤ differentIdeal (𝓞 H.K) (𝓞 H.E) := by
  intro x hx
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hx
  have := kc_diff_smul_mem H σ hc _ hx
  rwa [smul_inv_smul] at this
end Formalism.HC.Der
