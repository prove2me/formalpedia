-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:42.347672+00:00
-- url     : https://prove2.me/submissions/eb1a597a-1865-44f4-8616-3fa79cc99b2f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore

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
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution (p : Fin n → Fin n) (α β : Fin n → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p α β * X) i j = α i * X i j + β i * X (p i) j := by
  simp [dp, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
