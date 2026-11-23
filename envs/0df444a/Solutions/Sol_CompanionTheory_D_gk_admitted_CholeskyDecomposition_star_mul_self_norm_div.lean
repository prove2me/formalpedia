-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.star_mul_self_norm_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:47.07015+00:00
-- url     : https://prove2.me/submissions/3c2926ff-f749-4272-9300-d6fac150b5ef

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
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {x : 𝕜} (hx : x ≠ 0) :
    star ((‖x‖ : 𝕜) / x) * ((‖x‖ : 𝕜) / x) = 1 := by
  rw [star_div₀, RCLike.star_def, RCLike.conj_ofReal, div_mul_div_comm, RCLike.conj_mul, ← sq]
  exact div_self (pow_ne_zero 2 (by simpa using hx))
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
