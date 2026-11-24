-- Prove2me | solution 1 for Formalism.HC.D7.jac_2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:34.999811+00:00
-- url     : https://prove2.me/submissions/61621eb3-1cc8-43d6-a097-e69401b9ebe8

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution : jacobiSym ((2 : ℕ) : ℤ) d = 1 := by
  have h16 := hH.2.2.2.1
  have hd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, jacobiSym.at_two hd, ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : d % 2 ≠ 0 := by omega
  have h8 : d % 8 = 7 := by omega
  simp [h2, h8]
end Formalism.HC.D7
