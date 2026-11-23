-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:22.906801+00:00
-- url     : https://prove2.me/submissions/19409d24-bf59-4d39-be91-8243eba1d395

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_dp
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_diagonal

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
theorem _root_.solution (h : Adapted p b c) : dp p 0 c * dp p 0 c = 1 := by
  rw [dp_mul_dp h.invol, ← diagonal_one, ← dp_diagonal p]
  congr 1 <;> funext i <;> simp [h.symm, h.sq]
end Adapted
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
