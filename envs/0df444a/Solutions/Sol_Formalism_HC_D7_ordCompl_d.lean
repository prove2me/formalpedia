-- Prove2me | solution 1 for Formalism.HC.D7.ordCompl_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:18.1834+00:00
-- url     : https://prove2.me/submissions/a88f71f2-f26f-45e0-bb4d-cd2ee4681175

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
theorem _root_.solution : ordCompl[d] (2 ^ (e + 2) * q * d) = 2 ^ (e + 2) * q := by
  have hd := hH.2.1
  rw [show 2 ^ (e + 2) * q * d = d ^ 1 * (2 ^ (e + 2) * q) by ring]
  refine ordCompl_eq hd 1 ?_
  rw [hd.dvd_mul]
  have := hH.2.2.1
  have := hH.2.2.2.1
  rintro (h | h)
  · have h2 := Nat.le_of_dvd two_pos (hd.dvd_of_dvd_pow h)
    omega
  · have h3 := (Nat.prime_dvd_prime_iff_eq hd hH.1).mp h
    omega
end Formalism.HC.D7
