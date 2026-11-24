-- Prove2me | solution 1 for Formalism.HC.D7.jac_recip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:43.34784+00:00
-- url     : https://prove2.me/submissions/889f227c-8337-41ce-9aa6-a5096d3b31a9

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
namespace Formalism.HC.D7
theorem _root_.solution {r p : ℕ} (hr : r % 4 = 3) (hp : p % 2 = 1) : jacobiSym (-(r : ℤ)) p = jacobiSym (p : ℤ) r := by
  have hp' : Odd p := Nat.odd_iff.mpr hp
  have hr' : Odd r := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hp']
  rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h4 hr']
  · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hr h4]
    ring
end Formalism.HC.D7
