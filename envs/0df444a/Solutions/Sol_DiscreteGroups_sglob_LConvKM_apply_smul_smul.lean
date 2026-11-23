-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.apply_smul_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.894105+00:00
-- url     : https://prove2.me/submissions/653ccf4b-d558-41c9-bbf4-1dc5849d7104

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
variable (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
namespace DiscreteGroups.sglob.LConvKM
theorem _root_.solution (a : ℂ) (x y : M) : B (a • x) (a • y) = (starRingEnd ℂ) a * a * B x y := by
  simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  ring
end DiscreteGroups.sglob.LConvKM
