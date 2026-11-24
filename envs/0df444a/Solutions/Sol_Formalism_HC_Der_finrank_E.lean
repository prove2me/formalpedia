-- Prove2me | solution 1 for Formalism.HC.Der.finrank_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:44.371849+00:00
-- url     : https://prove2.me/submissions/57207396-9c9f-4942-a98c-1c26eef72a0a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Frame_natCard_GG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : Module.finrank ℚ H.E = 4 * φ.ord := by
  have := H.galois
  rw [← IsGalois.card_aut_eq_finrank, ← φ.natCard_GG]
  exact Nat.card_congr H.gal.toEquiv
end Formalism.HC.Der
