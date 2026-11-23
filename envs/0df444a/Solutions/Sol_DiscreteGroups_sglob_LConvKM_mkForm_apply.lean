-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.mkForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:29.520355+00:00
-- url     : https://prove2.me/submissions/bec84d5e-32c2-463f-b904-1156ebc06144

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
theorem _root_.solution (F : M → M → ℂ) (h : F ∈ (sesqSet : Set (M → M → ℂ))) (x y : M) :
    mkForm F h x y = F x y := rfl
end DiscreteGroups.sglob.LConvKM
