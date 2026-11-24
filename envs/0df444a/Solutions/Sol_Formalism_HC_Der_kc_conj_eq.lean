-- Prove2me | solution 1 for Formalism.HC.Der.kc_conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:37.206449+00:00
-- url     : https://prove2.me/submissions/ee9dfbfd-d8d6-4de2-8c63-44e5a72c9d16

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_gal_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_conj_iff


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
variable (C : HostCore H)
include C
namespace Formalism.HC.Der
theorem _root_.solution : haveI := C.cm; (IsCMField.complexConj H.E).restrictScalars ℚ = H.conj := by
  haveI := C.cm
  apply H.gal.injective
  rw [kc_gal_conj]
  let ψ : H.E →+* ℂ := (IsAlgClosed.lift : H.E →ₐ[ℚ] ℂ).toRingHom
  exact (C.conj_iff ψ _).mp (fun x => IsCMField.complexEmbedding_complexConj H.E ψ x)
end Formalism.HC.Der
