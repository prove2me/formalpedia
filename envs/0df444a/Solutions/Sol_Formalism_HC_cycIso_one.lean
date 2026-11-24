-- Prove2me | solution 1 for Formalism.HC.cycIso_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:59:20.981929+00:00
-- url     : https://prove2.me/submissions/530ffa65-74c3-4b6b-90af-e43a9975dd74

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup


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
theorem _root_.solution (e : ℕ) : cycIso e (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) :=
  Classical.choose_spec (hostGroup e).2.2.2.2.2.2.2.2
end Formalism.HC
