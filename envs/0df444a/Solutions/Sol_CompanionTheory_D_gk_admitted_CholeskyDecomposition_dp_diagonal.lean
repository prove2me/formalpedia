-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.888562+00:00
-- url     : https://prove2.me/submissions/5e28bb6c-de11-4acb-85c3-b78f58891065

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
theorem _root_.solution (p : Fin n → Fin n) (α : Fin n → ℂ) : dp p α 0 = diagonal α := by
  ext i j
  by_cases h : i = j
  · subst h; simp [dp]
  · simp [dp, h, Ne.symm h]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
