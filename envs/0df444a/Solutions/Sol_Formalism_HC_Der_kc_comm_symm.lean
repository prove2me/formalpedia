-- Prove2me | solution 1 for Formalism.HC.Der.kc_comm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:13:27.336782+00:00
-- url     : https://prove2.me/submissions/d6bdee92-ef28-43df-a475-a3fbbec6ad3f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcDiffSmulMem

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
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E)
    (hc : ∀ (τ : H.E ≃ₐ[H.K] H.E) (x : H.E), σ (τ x) = τ (σ x))
    (τ : H.E ≃ₐ[H.K] H.E) (x : H.E) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]
end Formalism.HC.Der
