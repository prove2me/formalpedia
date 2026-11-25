-- Prove2me | solution 1 for Formalism.HC.Frame.dig_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:53.527388+00:00
-- url     : https://prove2.me/submissions/098ea36a-42b0-4dc4-a9c8-f7c677d91411

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
theorem _root_.solution (s : ℕ) : φ.dig s = s • φ.a0 := rfl
end Formalism.HC.Frame
