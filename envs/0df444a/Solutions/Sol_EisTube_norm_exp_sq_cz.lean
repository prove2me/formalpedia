-- Prove2me | solution 1 for EisTube.norm_exp_sq_cz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:56.156872+00:00
-- url     : https://prove2.me/submissions/2f9c3429-cba4-4a96-9078-11fe98c858d8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone

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
theorem _root_.solution (x y : ι → ℝ) :
    ‖Complex.exp (∑ i, cz x y i ^ 2)‖ =
      Real.exp (∑ i, x i ^ 2) * Real.exp (-∑ i, y i ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Complex.re_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cz, sq, Complex.mul_re]
end EisTube
