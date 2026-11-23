-- Prove2me | solution 1 for Formalism.HC.Frame.natCard_GG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:20.670741+00:00
-- url     : https://prove2.me/submissions/307977be-c1ef-4ac8-813d-acf3b655555a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Theorems.Thm_Formalism_HC_Frame_natCard_A

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
open Formalism.FrobeniusOrbits
open Formalism.HC.Frame
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution : Nat.card φ.GG = 4 * φ.ord := by
  show Nat.card (G0 × φ.MA) = _
  rw [Nat.card_prod]
  have h0 : Nat.card G0 = 4 := by
    show Nat.card (ℤˣ × ℤˣ) = 4
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h2 : Nat.card φ.MA = φ.ord := φ.natCard_A
  rw [h0, h2]
end Formalism.HC.Frame
