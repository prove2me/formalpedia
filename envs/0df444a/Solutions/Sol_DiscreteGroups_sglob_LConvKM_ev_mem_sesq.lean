-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.ev_mem_sesq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.412361+00:00
-- url     : https://prove2.me/submissions/eacd1948-7df6-41fd-9441-9c3e8f72f879

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_mkForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] DiscreteGroups.sglob.LConvKM.mkForm_apply

set_option autoImplicit false
open Set ComplexConjugate
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvKM
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) : ev B ∈ (sesqSet : Set (M → M → ℂ)) := by
  refine ⟨⟨⟨fun x y z => ?_, fun a x z => ?_⟩, fun x y z => ?_⟩, fun a x y => ?_⟩ <;>
    simp [ev]
end DiscreteGroups.sglob.LConvKM
