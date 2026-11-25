-- Prove2me | solution 1 for Formalism.HC.frameCyc_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:23.911663+00:00
-- url     : https://prove2.me/submissions/0d9137df-5418-46ce-9dda-42e657c76f01

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_cycHom_apply
import Theorems.Thm_Formalism_HC_frameCyc_val

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
theorem _root_.solution (t : (frameCyc e a').A) :
    (frameCyc e a').h t = Additive.ofMul (hcl e (u5 (e + 2)) ^ t.val) := by
  rw [show (frameCyc e a').h t = cycHom e (frameCycIso e a' t) from rfl, cycHom_apply, frameCyc_val]
end Formalism.HC
