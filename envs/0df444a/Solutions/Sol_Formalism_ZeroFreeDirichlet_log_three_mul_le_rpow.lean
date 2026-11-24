-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_three_mul_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:59.598332+00:00
-- url     : https://prove2.me/submissions/8cefd2e7-787a-4dab-ab82-ed44d17909fa

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {N ε : ℝ} (hN : 0 ≤ N) (hε : 0 < ε) :
    Real.log (3 * N) ≤ 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
  have h := Real.log_le_rpow_div (x := 3 * N) (by positivity) (half_pos hε)
  rw [Real.mul_rpow (by norm_num) hN] at h
  have e : (3 : ℝ) ^ (ε / 2) * N ^ (ε / 2) / (ε / 2) = 2 * (3 : ℝ) ^ (ε / 2) / ε * N ^ (ε / 2) := by
    field_simp
  linarith
end Formalism.ZeroFreeDirichlet
