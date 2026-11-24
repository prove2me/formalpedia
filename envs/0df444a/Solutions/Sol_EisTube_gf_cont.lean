-- Prove2me | solution 1 for EisTube.gf_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:44.613798+00:00
-- url     : https://prove2.me/submissions/dc51ada6-a920-4bf4-acfa-3a2b48867844

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_continuous_cz_right
import Theorems.Thm_EisTube_cz_mem_tube

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
variable {P : Type*} [TopologicalSpace P]
namespace EisTube
theorem _root_.solution {Ω : Set (ι → ℝ)} {F : (ι → ℂ) → P → ℂ}
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) (p : P) {x : ι → ℝ} (hx : x ∈ Ω) :
    Continuous (fun y => gf F (cz x y) p) := by
  have : DifferentiableOn ℂ (fun z => gf F z p) (tube Ω) := by
    unfold gf
    exact (hhol p).mul (Differentiable.differentiableOn (by fun_prop))
  exact this.continuousOn.comp_continuous (continuous_cz_right x) (cz_mem_tube hx)
end EisTube
