-- Prove2me | solution 1 for Formalism.SL.P.SphereChartDerivatives.sn_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:00.768077+00:00
-- url     : https://prove2.me/submissions/85a53506-ff6e-4b6a-b34a-492961f50b23

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementLF
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last

set_option autoImplicit false
open Formalism Formalism.SL Formalism.SL.P
open MeasureTheory Formalism.SL.SB
open scoped ContDiff
open Formalism.SL.P.SphereChartDerivatives
variable {n : ℕ}
namespace Formalism.SL.P.SphereChartDerivatives
theorem _root_.solution (t : ℝ) (y : Fin n → ℝ) (k : Fin n) : sn t y (Fin.castSucc k) = y k := by
  simp [sn]
end Formalism.SL.P.SphereChartDerivatives
