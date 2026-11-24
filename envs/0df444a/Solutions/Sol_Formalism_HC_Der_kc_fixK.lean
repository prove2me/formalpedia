-- Prove2me | solution 1 for Formalism.HC.Der.kc_fixK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:34:12.991328+00:00
-- url     : https://prove2.me/submissions/60e89ed4-aa68-4e5c-9ed4-12f0a2c8bb47

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_mem_Psi_iff

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
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (hσ : H.gal σ ∈ φ.Psi) (x : H.K) : σ (x : H.E) = x := by
  have hs : H.sqd ∈ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun f hf => hf
  have hle : H.K ≤ IntermediateField.fixedField (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd) := by
    unfold HostRaw.K
    exact IntermediateField.adjoin_simple_le_iff.mpr hs
  have hx := hle x.2
  rw [IntermediateField.mem_fixedField_iff] at hx
  exact hx σ ((kc_mem_Psi_iff H σ).mp hσ)
end Formalism.HC.Der
