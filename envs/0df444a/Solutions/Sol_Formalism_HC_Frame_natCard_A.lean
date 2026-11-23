-- Prove2me | solution 1 for Formalism.HC.Frame.natCard_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:25.210948+00:00
-- url     : https://prove2.me/submissions/01ac6089-9fb6-4e0a-9f1e-1f76fc9d3116

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Theorems.Thm_Formalism_HC_Frame_card_A

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
theorem _root_.solution : Nat.card φ.A = φ.ord := by
  rw [Nat.card_eq_fintype_card, card_A]
end Formalism.HC.Frame
