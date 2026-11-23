-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.norm_le_polar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:41.195351+00:00
-- url     : https://prove2.me/submissions/2488c3b4-7c42-4a18-80cf-55c8fb21898c

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_norm_diag
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_polar

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
theorem _root_.solution (herm : ∀ x y, (starRingEnd ℂ) (B x y) = B y x) (psd : ∀ x, 0 ≤ (B x x).re)
    (x y : M) :
    4 * ‖B x y‖ ≤ (B (x + y) (x + y)).re + (B (x - y) (x - y)).re
      + (B (x + Complex.I • y) (x + Complex.I • y)).re + (B (x - Complex.I • y) (x - Complex.I • y)).re := by
  have h0 : ‖(4 : ℂ) * B x y‖ = 4 * ‖B x y‖ := by rw [norm_mul]; norm_num
  have h1 := norm_add_le (B (x + y) (x + y) - B (x - y) (x - y)
    - Complex.I * B (x + Complex.I • y) (x + Complex.I • y)) (Complex.I * B (x - Complex.I • y) (x - Complex.I • y))
  have h2 := norm_sub_le (B (x + y) (x + y) - B (x - y) (x - y))
    (Complex.I * B (x + Complex.I • y) (x + Complex.I • y))
  have h3 := norm_sub_le (B (x + y) (x + y)) (B (x - y) (x - y))
  simp only [norm_mul, Complex.norm_I, one_mul] at h1 h2
  rw [← polar B x y, h0] at h1
  simp only [norm_diag B herm psd] at h1 h2 h3
  linarith
end DiscreteGroups.sglob.LConvKM
