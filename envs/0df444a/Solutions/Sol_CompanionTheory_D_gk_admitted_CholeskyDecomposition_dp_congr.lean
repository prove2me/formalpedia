-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:24.234097+00:00
-- url     : https://prove2.me/submissions/5d809b4a-df6e-4f45-840a-63da397d3630

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
theorem _root_.solution {p : Fin n → Fin n} {α β α' β' : Fin n → ℂ}
    (h1 : ∀ i, p i = i → α i + β i = α' i + β' i) (h2 : ∀ i, p i ≠ i → α i = α' i ∧ β i = β' i) :
    dp p α β = dp p α' β' := by
  ext i j
  simp only [dp, Matrix.of_apply]
  by_cases h : p i = i
  · rw [h]
    split_ifs
    · exact h1 i h
    · rfl
  · rw [(h2 i h).1, (h2 i h).2]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
