-- Prove2me | solution 1 for Formalism.HC.cyclicFramePow_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:00.403537+00:00
-- url     : https://prove2.me/submissions/86466540-742d-416a-b0f7-097ecc543339

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_cyclicFramePow_order

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC
theorem _root_.solution (e j : ℕ) (hj : j ≤ e) : (cyclicFramePow e j).o = 2 ^ j := by
  show (cyclicFramePow e j).ord / (cyclicFramePow e j).n0 = _
  rw [cyclicFramePow_order e j hj]
  show 2 ^ e / 2 ^ (e - j) = _
  rw [Nat.pow_div (Nat.sub_le e j) two_pos, Nat.sub_sub_self hj]
end Formalism.HC
