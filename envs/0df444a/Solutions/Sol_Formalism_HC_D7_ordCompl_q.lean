-- Prove2me | solution 1 for Formalism.HC.D7.ordCompl_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:07:17.110817+00:00
-- url     : https://prove2.me/submissions/1b8f65bd-d441-453f-bde3-bb2e25dfc86f

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
theorem _root_.solution : ordCompl[q] (2 ^ (e + 2) * q * d) = 2 ^ (e + 2) * d := by
  have hq := hH.1
  rw [show 2 ^ (e + 2) * q * d = q ^ 1 * (2 ^ (e + 2) * d) by ring]
  refine ordCompl_eq hq 1 ?_
  rw [hq.dvd_mul]
  have := hH.2.2.1
  have := hH.2.2.2.1
  rintro (h | h)
  · have h2 := Nat.le_of_dvd two_pos (hq.dvd_of_dvd_pow h)
    omega
  · have h3 := (Nat.prime_dvd_prime_iff_eq hq hH.2.1).mp h
    omega
end Formalism.HC.D7
