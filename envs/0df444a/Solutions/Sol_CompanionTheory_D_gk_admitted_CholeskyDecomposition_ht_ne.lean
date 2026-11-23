-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.ht_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:45.903009+00:00
-- url     : https://prove2.me/submissions/e2aa34e4-13c8-469a-8b96-b8d22d1824a8

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
open CompanionTheory.D.gk.admitted.CholeskyDecomposition
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {ε : Fin n → Bool} {i : Fin n} (h : ε i.rev ≠ ε i) : 2 * (i : ℤ) + 1 - n ≠ 0 := by
  intro h2
  apply h
  have e : i.rev = i := by
    ext
    have h3 := Fin.val_rev i
    omega
  rw [e]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
