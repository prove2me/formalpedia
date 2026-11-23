-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.flip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:43.605399+00:00
-- url     : https://prove2.me/submissions/a603218f-27b5-4e39-9019-421f2c9f66e0

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
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {A g : Matrix (Fin n) (Fin n) ℂ} (hA : A * A = 1) (hg : gᴴ * A * g = A) : g * A * gᴴ = A := by
  have h1 : (A * gᴴ * A) * g = 1 := by
    calc (A * gᴴ * A) * g = A * (gᴴ * A * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hA]
  have h2 : g * (A * gᴴ * A) = 1 := mul_eq_one_comm.1 h1
  calc g * A * gᴴ = g * A * gᴴ * (A * A) := by rw [hA, Matrix.mul_one]
    _ = (g * (A * gᴴ * A)) * A := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h2, Matrix.one_mul]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
