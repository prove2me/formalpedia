-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_zero_of_unitary_blockTriangular
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:25.362103+00:00
-- url     : https://prove2.me/submissions/4543f568-b7a4-4357-90b6-d59bc507a074

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
theorem _root_.solution {b : Fin n → ℤ} {w : Matrix (Fin n) (Fin n) ℂ}
    (h1 : wᴴ * w = 1) (hw : w.BlockTriangular b) {i j : Fin n} (hij : b i ≠ b j) : w i j = 0 := by
  let _ : Invertible w := invertibleOfLeftInverse w wᴴ h1
  have hinv : w⁻¹ = wᴴ := inv_eq_left_inv h1
  have h2 : w⁻¹.BlockTriangular b := blockTriangular_inv_of_blockTriangular hw
  rw [hinv] at h2
  rcases lt_or_gt_of_ne hij with h | h
  · have := h2 h
    simpa [conjTranspose_apply] using this
  · exact hw h
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
