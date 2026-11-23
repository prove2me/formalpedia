-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.comb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:30.692518+00:00
-- url     : https://prove2.me/submissions/8f6570a6-752a-406f-96ee-3a3acd4ad79e

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
theorem _root_.solution (F G : M → M → ℂ) (a b : ℝ) (x y : M) :
    (a • F + b • G) x y = (a : ℂ) * F x y + (b : ℂ) * G x y := by
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
end DiscreteGroups.sglob.LConvKM
