-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_one_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:24.739246+00:00
-- url     : https://prove2.me/submissions/40c9b75c-7fb2-4302-b530-c6f35b188f8c

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
theorem _root_.solution {w : Matrix (Fin n) (Fin n) ℂ} (h1 : wᴴ * w = 1) (hw : w.PosSemidef) : w = 1 := by
  rw [hw.isHermitian.eq] at h1
  have hu : IsUnit (1 + w) := (PosDef.one.add_posSemidef hw).isUnit
  have : (1 + w) * (w - 1) = 0 := by
    rw [mul_sub, add_mul, h1]; simp [add_comm]
  exact sub_eq_zero.1 (hu.mul_right_eq_zero.1 this)
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
