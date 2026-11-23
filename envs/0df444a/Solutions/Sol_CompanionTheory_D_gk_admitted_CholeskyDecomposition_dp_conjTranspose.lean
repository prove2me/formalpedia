-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.dp_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:41.565273+00:00
-- url     : https://prove2.me/submissions/6f0c6c99-4415-4ff9-959b-1d17ae1d34f5

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
theorem _root_.solution {p : Fin n → Fin n} (hp : ∀ i, p (p i) = i) (α β : Fin n → ℂ) :
    (dp p α β)ᴴ = dp p (fun i => star (α i)) (fun i => star (β (p i))) := by
  ext i j
  simp only [dp, conjTranspose_apply, Matrix.of_apply, star_add]
  congr 1
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · by_cases h : j = p i
    · subst h; simp [hp]
    · have : i ≠ p j := fun h' => h (by rw [h', hp])
      simp [h, this]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
