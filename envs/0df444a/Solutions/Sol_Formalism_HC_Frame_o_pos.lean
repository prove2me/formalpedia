-- Prove2me | solution 1 for Formalism.HC.Frame.o_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:42:32.854361+00:00
-- url     : https://prove2.me/submissions/d2902a8b-a40d-477a-9fc6-03c8039437f3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_n0_pos
import Theorems.Thm_Formalism_HC_Frame_cyclic_order_dvd_exponent
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
private theorem ord_pos' : 0 < φ.ord := by
  rw [← natCard_A_eq_ord]
  exact Nat.card_pos
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution : 0 < φ.o := Nat.div_pos (Nat.le_of_dvd (ord_pos' φ) φ.cyclic_order_dvd_exponent) φ.n0_pos
end Formalism.HC.Frame
