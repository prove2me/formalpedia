-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_two_le_log_mul_abs_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:11.046539+00:00
-- url     : https://prove2.me/submissions/c6c4d88b-b4cb-4f03-9b14-cb886461db48

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZFRDirichletOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_one_le_natCast

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
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]
end Formalism.ZeroFreeDirichlet
