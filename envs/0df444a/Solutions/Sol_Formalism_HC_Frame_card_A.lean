-- Prove2me | solution 1 for Formalism.HC.Frame.card_A
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:44.353025+00:00
-- url     : https://prove2.me/submissions/62719d4d-3e48-44c8-ae91-e7fd97b3575e

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection

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
theorem _root_.solution : Fintype.card φ.A = φ.ord := by
  exact Fintype.card_fin φ.ord
end Formalism.HC.Frame
