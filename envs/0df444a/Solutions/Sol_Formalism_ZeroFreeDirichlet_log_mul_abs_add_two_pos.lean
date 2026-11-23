-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_mul_abs_add_two_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:56.726653+00:00
-- url     : https://prove2.me/submissions/acad0119-12a9-443d-aaea-f34d6b855e10

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_two_le_log_mul_abs_add_two

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
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)
end Formalism.ZeroFreeDirichlet
