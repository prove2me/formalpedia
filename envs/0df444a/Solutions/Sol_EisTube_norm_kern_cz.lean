-- Prove2me | solution 1 for EisTube.norm_kern_cz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:51.679445+00:00
-- url     : https://prove2.me/submissions/ebabcf34-f902-410d-877f-a4b9b5a66633

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_sum_cz_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]
namespace EisTube
theorem _root_.solution (x y t : ι → ℝ) :
    ‖kern (cz x y) t‖ = Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by
  rw [kern, sum_cz_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]
end EisTube
