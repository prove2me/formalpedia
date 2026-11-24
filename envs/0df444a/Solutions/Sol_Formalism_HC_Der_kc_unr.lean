-- Prove2me | solution 1 for Formalism.HC.Der.kc_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:52:54.283979+00:00
-- url     : https://prove2.me/submissions/fa8e4640-a96a-4834-a6d5-036c8be5bd0d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase
import Theorems.Thm_Formalism_HC_Der_kc_conj_eq
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


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
theorem _root_.solution : haveI := C.cm; ∀ P : Ideal (𝓞 H.E), P.IsPrime → P ≠ ⊥ →
    ¬ ∀ x : 𝓞 H.E, IsCMField.complexConj H.E • x - x ∈ P := by
  haveI := C.cm
  intro P hP hne h
  apply C.unramEF P hP hne
  intro x
  have e : H.conj • x = IsCMField.complexConj H.E • x := by
    rw [← kc_conj_eq H C]
    rfl
  rw [e]
  exact h x
end Formalism.HC.Der
