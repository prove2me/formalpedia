-- Prove2me | solution 1 for EisTube.exp_cz_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:02.116655+00:00
-- url     : https://prove2.me/submissions/af95e10f-7cc2-41c1-ad6f-070b5adc3940

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
    Complex.exp (2 * (Real.pi : ℂ) * ∑ i, cz x y i * t i) =
      Complex.exp (2 * (Real.pi : ℂ) * ∑ i, ((x i : ℂ)) * t i) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (y i : ℂ) * t i) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [cz, add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
end EisTube
