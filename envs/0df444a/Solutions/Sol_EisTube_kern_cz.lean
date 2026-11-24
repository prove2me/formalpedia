-- Prove2me | solution 1 for EisTube.kern_cz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:06.760182+00:00
-- url     : https://prove2.me/submissions/9ce9c099-1ddf-48bc-87b3-7f3ffdeb1354

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
theorem _root_.solution (x y t : ι → ℝ) :
    kern (cz x y) t = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (y i : ℂ) * t i) *
      Complex.exp (-(2 * (Real.pi : ℂ)) * ∑ i, (x i : ℂ) * t i) := by
  rw [kern, ← Complex.exp_add]
  congr 1
  simp only [cz, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
end EisTube
