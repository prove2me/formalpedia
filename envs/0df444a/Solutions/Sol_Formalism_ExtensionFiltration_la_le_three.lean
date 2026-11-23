-- Prove2me | solution 1 for Formalism.ExtensionFiltration.la_le_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:35.991835+00:00
-- url     : https://prove2.me/submissions/baf52999-69d5-4fa9-a693-95823c426322

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
open Finset Module NumberField
namespace Formalism.ExtensionFiltration
theorem _root_.solution (x eps L b a rd La : ℝ) (hx : 1 ≤ x) (hL : L = x ^ eps) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hrdL : Real.log rd ≤ L) (hlx : Real.log x ≤ L)
    (hLa : La = Real.log (a * rd)) : La ≤ 3 * x ^ eps := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hrd0 : 0 < rd := lt_of_lt_of_le one_pos hrd
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlb : Real.log b = L := by rw [hb, Real.log_exp]
  rw [hLa, ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hlb, ← hL]
  linarith
end Formalism.ExtensionFiltration
