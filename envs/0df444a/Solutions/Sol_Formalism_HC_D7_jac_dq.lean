-- Prove2me | solution 1 for Formalism.HC.D7.jac_dq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:46.914816+00:00
-- url     : https://prove2.me/submissions/cc50c484-4db4-4531-a8f7-5c2bd4dfb4e4

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
theorem _root_.solution : jacobiSym (d : ℤ) q = -1 := by
  have h := hH.2.2.2.2
  have h8 := hH.2.2.1
  have hq : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hq, ZMod.χ₄_nat_three_mod_four (by omega)] at h
  linarith
end Formalism.HC.D7
