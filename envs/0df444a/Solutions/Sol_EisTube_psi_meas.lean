-- Prove2me | solution 1 for EisTube.psi_meas
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:40:58.610803+00:00
-- url     : https://prove2.me/submissions/f98f1118-084c-49c3-9c3b-426f44ec0d90

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_gf_cont

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
    (hhol : ∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) {x₀ : ι → ℝ} (h₀ : x₀ ∈ Ω) (p : P) :
    AEStronglyMeasurable (psiAt F x₀ p) := by
  have hc : Continuous (fun q : (ι → ℝ) × (ι → ℝ) => gf F (cz x₀ q.2) p * kern (cz x₀ q.2) q.1) := by
    refine ((gf_cont hhol p h₀).comp continuous_snd).mul ?_
    unfold kern cz; fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
end EisTube
