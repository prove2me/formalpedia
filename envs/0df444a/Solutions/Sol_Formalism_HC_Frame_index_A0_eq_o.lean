-- Prove2me | solution 1 for Formalism.HC.Frame.index_A0_eq_o
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:02:39.130357+00:00
-- url     : https://prove2.me/submissions/cc48b978-3994-45d9-8374-deb719a8661b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_n0_pos
import Theorems.Thm_Formalism_HC_Frame_exponent_eq_index_mul_cyclic_order
import Theorems.Thm_Formalism_HC_Frame_natCard_cyclic_subgroup
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
theorem _root_.solution : φ.A0.index = φ.o := by
  have h := φ.A0.card_mul_index
  rw [φ.natCard_cyclic_subgroup, natCard_A_eq_ord, φ.exponent_eq_index_mul_cyclic_order] at h
  exact Nat.eq_of_mul_eq_mul_left φ.n0_pos (h.trans (mul_comm _ _))
end Formalism.HC.Frame
