-- Prove2me | solution 1 for DiscreteGroups.sglob.LConvKM.re_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:41.387632+00:00
-- url     : https://prove2.me/submissions/3de9e4d3-052e-4463-9acd-3c7f28242e1c

import Mathlib
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvKMCore
import Theorems.Thm_DiscreteGroups_sglob_LConvKM_apply_smul_smul

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
theorem _root_.solution (a : ℂ) (x : M) : (B (a • x) (a • x)).re = Complex.normSq a * (B x x).re := by
  rw [apply_smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]
end DiscreteGroups.sglob.LConvKM
