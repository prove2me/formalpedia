-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.isUpperTriangular_conjTranspose_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:46.863045+00:00
-- url     : https://prove2.me/submissions/494d57de-e3e1-4b5d-a2be-1e6130820b9d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {A : Matrix n n 𝕜} :
    Aᴴ.IsUpperTriangular ↔ A.IsLowerTriangular := by
  constructor
  · intro h i j hij
    have := h (i := j) (j := i) (OrderDual.toDual_lt_toDual.1 hij)
    simpa [conjTranspose_apply] using this
  · intro h i j hij
    have := h (show OrderDual.toDual i < OrderDual.toDual j from hij)
    simp [conjTranspose_apply, this]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
