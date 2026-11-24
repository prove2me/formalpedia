-- Prove2me | solution 1 for Formalism.HC.cycIso_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:39.016356+00:00
-- url     : https://prove2.me/submissions/4c18a8e4-21ab-4cd7-9a27-a5b952443622

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_HC_cycIso_one

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
    cycIso e (Multiplicative.ofAdd i) = hcl e (u5 (e + 2)) ^ i.val := by
  haveI : NeZero (2 ^ e) := ⟨pow_ne_zero _ two_ne_zero⟩
  have h1 : Multiplicative.ofAdd i = (Multiplicative.ofAdd (1 : ZMod (2 ^ e))) ^ i.val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  rw [h1, map_pow, cycIso_one]
end Formalism.HC
