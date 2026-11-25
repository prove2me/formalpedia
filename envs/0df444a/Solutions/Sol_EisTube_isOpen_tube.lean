-- Prove2me | solution 1 for EisTube.isOpen_tube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:21:09.038217+00:00
-- url     : https://prove2.me/submissions/3a726923-38d9-42a4-8443-a294078694ee

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
import Theorems.Thm_EisTube_continuous_reV

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
theorem _root_.solution {Ω : Set (ι → ℝ)} (hΩ : IsOpen Ω) : IsOpen (tube Ω) :=
  hΩ.preimage continuous_reV
end EisTube
