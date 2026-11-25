-- Prove2me | solution 1 for Formalism.HC.frameCyc_twoGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:57:32.95899+00:00
-- url     : https://prove2.me/submissions/9cc5630c-d0d4-4acf-9d86-97e6329eddbd

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
variable (e : ℕ) (a' : ZMod (2 ^ e))
namespace Formalism.HC
theorem _root_.solution : (frameCyc e a').TwoGroup := ⟨e, rfl⟩
end Formalism.HC
