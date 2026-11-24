-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrders_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:57.622875+00:00
-- url     : https://prove2.me/submissions/5505da5e-5179-48ef-b401-3c1ddc04f776

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_orderOf_hH_dvd
import Theorems.Thm_Formalism_FrobeniusOrbits_hostOrders


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (a : φ.MA) (j : ℕ) (l : ℤ) (u : (ZMod (2 ^ (φ.e + 2)))ˣ)
    (hu : (u : ZMod (2 ^ (φ.e + 2))) = (l : ZMod _)) (ha : φ.hH a = hcl φ.e u) (hj : orderOf a ≤ 2 ^ j) :
    (l : ZMod (2 ^ (φ.e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (φ.e + 2 - j))) = -1 := by
  have h1 : orderOf (φ.hH a) ≤ 2 ^ j :=
    le_trans (Nat.le_of_dvd (orderOf_pos a) (φ.orderOf_hH_dvd a)) hj
  rw [ha] at h1
  exact ((Formalism.FrobeniusOrbits.hostOrders φ.e).1 j l u hu).1 h1
end Formalism.HC.Frame
