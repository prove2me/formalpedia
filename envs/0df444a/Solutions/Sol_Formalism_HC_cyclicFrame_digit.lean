-- Prove2me | solution 1 for Formalism.HC.cyclicFrame_digit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:20.478691+00:00
-- url     : https://prove2.me/submissions/247ca068-bfc8-4a7a-97d2-07a3c6c52c29

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_frameCyclic_generator

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
theorem _root_.solution (e s : ℕ) : frameCycIso e 1 ((frameCyc e 1).dig s) = (s : ZMod (2 ^ e)) := by
  show frameCycIso e 1 (s • (frameCyc e 1).a0) = _
  rw [map_nsmul, frameCyclic_generator, nsmul_one]
end Formalism.HC
