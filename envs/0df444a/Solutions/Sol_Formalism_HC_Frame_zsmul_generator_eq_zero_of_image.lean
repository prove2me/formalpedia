-- Prove2me | solution 1 for Formalism.HC.Frame.zsmul_generator_eq_zero_of_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:29.375987+00:00
-- url     : https://prove2.me/submissions/561923a5-b61b-4f46-a935-228d5b0c74e4

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
theorem _root_.solution (k : ℤ) (hk : φ.h (k • φ.a0) = 0) : k • φ.a0 = 0 := by
  exact φ.zsmul_generator_eq_zero_of_projection k hk
end Formalism.HC.Frame
