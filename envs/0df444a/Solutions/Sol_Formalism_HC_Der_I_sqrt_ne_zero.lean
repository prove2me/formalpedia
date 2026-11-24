-- Prove2me | solution 1 for Formalism.HC.Der.I_sqrt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:15.443632+00:00
-- url     : https://prove2.me/submissions/6de95d99-b8d5-4e74-9b29-22bcf0e25d4a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : Complex.I * (Real.sqrt H.d : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr h).ne')
end Formalism.HC.Der
