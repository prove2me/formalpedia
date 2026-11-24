-- Prove2me | solution 1 for Formalism.HC.cycHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:37.883243+00:00
-- url     : https://prove2.me/submissions/66d0fb6e-85ef-46d2-9a0f-809240d0919f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_cycIso_apply

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
theorem _root_.solution (e : ℕ) (i : ZMod (2 ^ e)) :
    cycHom e i = Additive.ofMul (hcl e (u5 (e + 2)) ^ i.val) := by
  show Additive.ofMul (cycIso e (Multiplicative.ofAdd i)) = _
  rw [cycIso_apply]
end Formalism.HC
