-- Prove2me | solution 1 for Formalism.SL.P.SphereChartDerivatives.sn_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:39.514681+00:00
-- url     : https://prove2.me/submissions/ccd26e1a-19e9-420a-b36f-33165063446a

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementLF
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SL Formalism.SL.P
open MeasureTheory Formalism.SL.SB
open scoped ContDiff
open Formalism.SL.P.SphereChartDerivatives
variable {n : ℕ}
namespace Formalism.SL.P.SphereChartDerivatives
theorem _root_.solution (t : ℝ) (y : Fin n → ℝ) : sn t y (Fin.last n) = t := by simp [sn]
end Formalism.SL.P.SphereChartDerivatives
