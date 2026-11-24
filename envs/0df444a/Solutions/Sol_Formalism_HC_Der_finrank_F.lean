-- Prove2me | solution 1 for Formalism.HC.Der.finrank_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:22:24.533823+00:00
-- url     : https://prove2.me/submissions/8ee2e4ae-e034-4bc9-aa43-f7f6126aba43

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_cm
import Theorems.Thm_Formalism_HC_Der_finrank_E

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : Module.finrank ℚ H.F = 2 * φ.ord := by
  have := cm H
  have h0 := Module.finrank_mul_finrank ℚ H.F H.E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two H.F H.E, finrank_E] at h0
  omega
end Formalism.HC.Der
