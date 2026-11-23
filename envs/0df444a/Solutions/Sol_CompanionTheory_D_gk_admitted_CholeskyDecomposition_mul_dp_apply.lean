-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.mul_dp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:34.139135+00:00
-- url     : https://prove2.me/submissions/cd521c6b-76ed-42b1-bab3-116fee470a1b

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
theorem _root_.solution {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (β : Fin n → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : (X * dp p 0 β) i j = X i (p j) * β (p j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (p j)]
  · simp [dp, hp]
  · intro k _ hk
    have : j ≠ p k := fun h => hk (by rw [h, hp])
    simp [dp, this]
  · simp
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
