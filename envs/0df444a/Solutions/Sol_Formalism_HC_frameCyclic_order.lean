-- Prove2me | solution 1 for Formalism.HC.frameCyclic_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:31:32.218586+00:00
-- url     : https://prove2.me/submissions/8fcd83d1-e8dc-40a0-833c-5ad90c578b6c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_Frame_ofEquiv_order

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
theorem _root_.solution : (frameCyc e a').n0 = addOrderOf a' :=
  Frame.ofEquiv_order e (idxZMod (2 ^ e)) (cycHom e) (cycHom_bijective e).2 a' (cycHom_ker e a')
end Formalism.HC
