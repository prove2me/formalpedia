-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.norm_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.991895+00:00
-- url     : https://prove2.me/submissions/69455497-198a-450f-b67a-91439fbe605d

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
theorem _root_.solution (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re) (x : M) :
    ‖B x x‖ = (B x x).re := by
  have h : B x x = ((B x x).re : ℂ) := (Complex.conj_eq_iff_re.mp (herm x x)).symm
  conv_lhs => rw [h]
  rw [Complex.norm_real, Real.norm_of_nonneg (psd x)]
end DiscreteGroups.sglob.LConvKM
