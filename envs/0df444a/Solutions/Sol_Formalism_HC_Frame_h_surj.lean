-- Prove2me | solution 1 for Formalism.HC.Frame.h_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:11.364818+00:00
-- url     : https://prove2.me/submissions/ae89b0b0-0811-42bf-a732-0586833cc0a3

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
theorem _root_.solution : Function.Surjective φ.h := by
  exact φ.projection_surjective_field
end Formalism.HC.Frame
