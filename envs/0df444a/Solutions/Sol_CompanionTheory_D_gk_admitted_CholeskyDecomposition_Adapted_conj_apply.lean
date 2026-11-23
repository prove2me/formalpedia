-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:31.33979+00:00
-- url     : https://prove2.me/submissions/660684fb-c90c-4b0f-8efe-5ad316833ab4

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_mul_dp_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
namespace Adapted
theorem _root_.solution (h : Adapted p b c) (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p 0 c * Bᴴ * dp p 0 c) i j = c i * c j * star (B (p j) (p i)) := by
  rw [mul_dp_apply h.invol, dp_mul_apply, h.symm, conjTranspose_apply, conjTranspose_apply]
  simp only [Pi.zero_apply]
  ring
end Adapted
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
