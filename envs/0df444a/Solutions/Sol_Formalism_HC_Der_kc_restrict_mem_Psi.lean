-- Prove2me | solution 1 for Formalism.HC.Der.kc_restrict_mem_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:13.834031+00:00
-- url     : https://prove2.me/submissions/79a106c5-91d5-4d81-ab6d-8f39f89a9fa5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Der_kc_sqd_mem

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
theorem _root_.solution (σ : H.E ≃ₐ[H.K] H.E) : H.gal (σ.restrictScalars ℚ) ∈ φ.Psi := by
  rw [kc_mem_Psi_iff]
  exact σ.commutes ⟨H.sqd, kc_sqd_mem H⟩
end Formalism.HC.Der
