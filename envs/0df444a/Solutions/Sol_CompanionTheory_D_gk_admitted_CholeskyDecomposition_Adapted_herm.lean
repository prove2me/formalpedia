-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.herm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:16.858806+00:00
-- url     : https://prove2.me/submissions/d22a456d-f157-453a-b6c1-bea0a5e5f55f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_dp_conjTranspose

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
namespace Adapted
theorem _root_.solution (h : Adapted p b c) : (dp p 0 c)ᴴ = dp p 0 c := by
  rw [dp_conjTranspose h.invol]
  congr 1 <;> funext i <;> simp only [h.symm, h.star_eq, Pi.zero_apply, star_zero]
end Adapted
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
