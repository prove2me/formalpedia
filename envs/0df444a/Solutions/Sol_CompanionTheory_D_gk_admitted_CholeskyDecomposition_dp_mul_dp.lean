-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_mul_dp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:34.082311+00:00
-- url     : https://prove2.me/submissions/01172ef1-78c0-40e8-97bd-8c2362592eb3

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_mul_apply

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
theorem _root_.solution {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β α' β' : Fin n → ℂ) :
    dp p α β * dp p α' β' =
      dp p (fun i => α i * α' i + β i * β' (p i)) (fun i => α i * β' i + β i * α' (p i)) := by
  ext i j
  rw [dp_mul_apply]
  simp only [dp, Matrix.of_apply, hp]
  split_ifs <;> ring
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
