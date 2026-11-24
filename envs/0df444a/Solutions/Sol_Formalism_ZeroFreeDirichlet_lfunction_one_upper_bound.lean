-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.lfunction_one_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:04.011804+00:00
-- url     : https://prove2.me/submissions/314688d6-46ed-4e50-9911-45ba38246e03

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LFunctionOneUpperBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_norm_le_near_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_three_le_modulus_of_ne_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_two_le_log_three_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : LFunctionOneUpperBound := by
  refine ⟨38 * Real.exp (3 / 2), ?_⟩
  intro q _ χ hχ
  have hq : 3 ≤ q := three_le_modulus_of_ne_one χ hχ
  have hlog : 2 ≤ Real.log (3 * (q : ℝ)) := two_le_log_three_mul q hq
  have hd : 0 < 3 / (2 * Real.log (3 * (q : ℝ))) := div_pos (by norm_num) (by linarith)
  exact lfunction_norm_le_near_one χ hχ 1 (by rw [Complex.one_re]; linarith)
    (by rw [Complex.one_re]; norm_num) (by rw [norm_one]; norm_num)
end Formalism.ZeroFreeDirichlet
