-- Prove2me | solution 1 for EisTube.gauss2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:16.838958+00:00
-- url     : https://prove2.me/submissions/5be94b4f-d661-4573-b1b7-a1ec251ad351

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_gaussInt
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_gaussInt


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
theorem _root_.solution : Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 2)) := by
  have := gaussInt ι (1 / 2) (by norm_num)
  refine this.congr (ae_of_all _ fun y => ?_)
  simp only
  congr 1; ring
end EisTube
