-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.tri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:38.196318+00:00
-- url     : https://prove2.me/submissions/3e50be27-f4e5-4ab9-bded-3360c4f24de0

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
namespace Adapted
theorem _root_.solution (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id) :
    B.BlockTriangular b := fun _ _ hij => hB (h.mono.reflect_lt hij)
end Adapted
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
