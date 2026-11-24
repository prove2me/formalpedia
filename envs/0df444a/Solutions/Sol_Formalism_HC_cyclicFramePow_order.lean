-- Prove2me | solution 1 for Formalism.HC.cyclicFramePow_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:21.885432+00:00
-- url     : https://prove2.me/submissions/05c544da-f60e-47c0-85b7-6f1bf7a61c76

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_frameCyclic_order
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC
theorem _root_.solution (e j : ℕ) (hj : j ≤ e) : (cyclicFramePow e j).n0 = 2 ^ (e - j) := by
  show (frameCyc e (2 ^ j)).n0 = _
  rw [frameCyclic_order]
  have h1 : ((2 ^ j : ℕ) : ZMod (2 ^ e)) = (2 : ZMod (2 ^ e)) ^ j := by simp
  rw [← h1, ZMod.addOrderOf_coe _ (pow_ne_zero _ two_ne_zero),
    Nat.gcd_eq_right (Nat.pow_dvd_pow 2 hj), Nat.pow_div hj two_pos]
end Formalism.HC
