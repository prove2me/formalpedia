-- Prove2me | solution 1 for Formalism.HC.cyclicFrame_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:07.817817+00:00
-- url     : https://prove2.me/submissions/bb3b17b4-0358-40df-9d49-30301b40c839

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_frameCyc_ord
import Theorems.Thm_Formalism_HC_frameCyclic_order

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
theorem _root_.solution (e : ℕ) : (cyclicFrame e).o = 1 := by
  show (frameCyc e 1).ord / (frameCyc e 1).n0 = 1
  rw [frameCyclic_order, ZMod.addOrderOf_one, frameCyc_ord]
  exact Nat.div_self (pow_pos two_pos e)
end Formalism.HC
