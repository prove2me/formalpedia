-- Prove2me | solution 1 for Formalism.HC.Der.split_QSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:49:10.080673+00:00
-- url     : https://prove2.me/submissions/e9c4b9bd-a77f-45af-89a5-70e581c80748

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
theorem _root_.solution (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2) (h : l ∣ H.QS * H.q) : jacobiSym (-(H.d : ℤ)) l = 1 := by
  rcases (Nat.Prime.dvd_mul hl).mp h with h1 | h1
  · exact H.QS_split l hl hl2 h1
  · have hlq : l = H.q := (Nat.prime_dvd_prime_iff_eq hl H.hyp.1).mp h1
    rw [hlq]
    exact H.hyp.2.2.2.2
end Formalism.HC.Der
