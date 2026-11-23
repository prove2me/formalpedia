-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.re_add_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:41.213523+00:00
-- url     : https://prove2.me/submissions/e633f9f1-9fd5-41b7-bc6f-3519cb649fbb

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_diag_expand_add

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
theorem _root_.solution (psd : ∀ x, 0 ≤ (B x x).re) (x y : M) :
    (B (x + y) (x + y)).re ≤ 2 * (B x x).re + 2 * (B y y).re := by
  have h := congrArg Complex.re (diag_expand_add B x y)
  simp only [Complex.add_re] at h
  linarith [psd (x - y)]
end DiscreteGroups.sglob.LConvKM
