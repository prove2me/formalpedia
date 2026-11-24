-- Prove2me | solution 1 for Formalism.HC.Der.cop_QSq_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:17.442051+00:00
-- url     : https://prove2.me/submissions/1336acde-7f74-4551-b5ce-d70047d51bfa

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

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
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : Nat.Coprime (H.QS * H.q) H.d := by
  have hqd : H.q ≠ H.d := by
    intro h
    have h1 := H.hyp.2.2.1
    have h2 := H.hyp.2.2.2.1
    rw [h] at h1
    omega
  have hq : Nat.Coprime H.q H.d := (Nat.coprime_primes H.hyp.1 H.hyp.2.1).mpr hqd
  exact Nat.Coprime.mul (Nat.Coprime.coprime_mul_left_right H.QS_coprime) hq
end Formalism.HC.Der
