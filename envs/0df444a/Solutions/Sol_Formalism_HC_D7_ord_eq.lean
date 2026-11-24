-- Prove2me | solution 1 for Formalism.HC.D7.ord_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:28:22.984868+00:00
-- url     : https://prove2.me/submissions/ad055dc3-44cd-43dc-b44a-51fe20cece77

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Theorems.Thm_Formalism_FrobeniusOrbits_hostGroup
import Theorems.Thm_Formalism_HC_Frame_natCard_A


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.HC.D7
variable (φ : Frame) (hinj : Function.Injective φ.h)
include hinj
namespace Formalism.HC.D7
theorem _root_.solution : φ.ord = 2 ^ φ.e := by
  have h1 := Nat.card_congr (hIso φ hinj).toEquiv
  rw [(hostGroup φ.e).2.2.2.2.2.2.1] at h1
  rw [← h1, ← φ.natCard_A]
  exact Nat.card_congr Multiplicative.ofAdd
end Formalism.HC.D7
