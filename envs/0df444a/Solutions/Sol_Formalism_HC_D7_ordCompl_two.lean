-- Prove2me | solution 1 for Formalism.HC.D7.ordCompl_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:48.65287+00:00
-- url     : https://prove2.me/submissions/de103726-fb2f-4948-9c03-c66830c96050

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_ordCompl_eq

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
theorem _root_.solution : ordCompl[2] (2 ^ (e + 2) * q * d) = q * d := by
  rw [mul_assoc]
  refine ordCompl_eq Nat.prime_two (e + 2) ?_
  rw [Nat.Prime.dvd_mul Nat.prime_two]
  have := hH.2.2.1
  have := hH.2.2.2.1
  omega
end Formalism.HC.D7
