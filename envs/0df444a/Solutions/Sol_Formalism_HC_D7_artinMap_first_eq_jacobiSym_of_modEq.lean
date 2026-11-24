-- Prove2me | solution 1 for Formalism.HC.D7.artinMap_first_eq_jacobiSym_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:03:14.418132+00:00
-- url     : https://prove2.me/submissions/05a509bb-8bd1-4ec8-906b-1ac323c15c70

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_jac_congr

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
theorem _root_.solution (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q]) :
    (((art0 e hH u).1.1 : ℤˣ) : ℤ) = jacobiSym (y : ℤ) q := by
  haveI := neZeroN e hH
  have h : (art0 e hH u).1.1 = sgnN hH.1 (q_dvd e q d) u := rfl
  rw [h, sgnN_val]
  exact jac_congr hu
end Formalism.HC.D7
