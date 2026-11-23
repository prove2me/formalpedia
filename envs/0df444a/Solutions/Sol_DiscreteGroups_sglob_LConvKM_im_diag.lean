-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.im_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.488279+00:00
-- url     : https://prove2.me/submissions/18119b2c-1583-4c32-a528-bff4eba4c113

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
theorem _root_.solution (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (x : M) : (B x x).im = 0 := by
  have h := congrArg Complex.im (herm x x)
  rw [Complex.conj_im] at h
  linarith
end DiscreteGroups.sglob.LConvKM
