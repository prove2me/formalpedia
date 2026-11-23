-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.continuous_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:50.208908+00:00
-- url     : https://prove2.me/submissions/c8ff095c-a2b4-4403-8892-090820ad17d7

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (a b : M) : Continuous fun F : M → M → ℂ => F a b :=
  (continuous_apply b).comp (continuous_apply a)
end DiscreteGroups.sglob.LConvKM
