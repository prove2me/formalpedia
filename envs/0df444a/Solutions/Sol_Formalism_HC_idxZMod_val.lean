-- Prove2me | solution 1 for Formalism.HC.idxZMod_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:25.164942+00:00
-- url     : https://prove2.me/submissions/2d84688a-620e-45a3-bb9b-65f55e4cde78

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator

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
theorem _root_.solution (n : ℕ) [NeZero n] (t : Idx n) : (idxZMod n t).val = Fin.val (n := n) t := by
  rcases n with _ | k
  · exact (NeZero.ne 0 rfl).elim
  · rfl
end Formalism.HC
