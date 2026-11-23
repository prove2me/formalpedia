-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_mem_unit_interval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:10.506104+00:00
-- url     : https://prove2.me/submissions/015c8180-d8ad-47f7-8c3f-62df7b0564e3

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SumVonMangoldtNotCoprimeLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LeOfSecondDifferenceBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PsiChiBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {c₀ y : ℝ} (hc0 : 0 < c₀) :
    0 < Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ∧
      Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ≤ 1 := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.2 ?_⟩
  have := mul_nonneg hc0.le (Real.sqrt_nonneg (Real.log y))
  linarith
end Formalism.ZeroFreeDirichlet
