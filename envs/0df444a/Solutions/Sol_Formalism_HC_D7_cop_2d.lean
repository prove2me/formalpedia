-- Prove2me | solution 1 for Formalism.HC.D7.cop_2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:07.596521+00:00
-- url     : https://prove2.me/submissions/5f0881aa-7fce-49b0-89fc-75dee530b066

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution : Nat.Coprime (2 ^ (e + 2)) d := by
  apply Nat.Coprime.pow_left
  rw [Nat.coprime_primes Nat.prime_two hH.2.1]
  have := hH.2.2.2.1
  omega
end Formalism.HC.D7
