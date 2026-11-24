-- Prove2me | solution 1 for Formalism.HC.Frame.natCard_MA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:53:58.361829+00:00
-- url     : https://prove2.me/submissions/be442838-1f6f-46e3-b5b9-63cd111f51ae

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem natCard_A_eq_ord : Nat.card φ.A = φ.ord := by
  show Nat.card (Fin φ.ord) = φ.ord
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution : Nat.card φ.MA = φ.ord := by
  rw [Nat.card_congr (Multiplicative.ofAdd (α := φ.A)).symm]
  exact natCard_A_eq_ord φ
end Formalism.HC.Frame
