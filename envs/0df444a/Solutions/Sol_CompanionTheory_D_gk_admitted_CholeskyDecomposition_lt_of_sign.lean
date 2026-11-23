-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.lt_of_sign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:46.798622+00:00
-- url     : https://prove2.me/submissions/89ed775c-f221-45b0-9326-2a78216d4175

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
theorem _root_.solution {ε : Fin n → Bool} (hε : Monotone ε) {i j : Fin n} (hi : ε i = false) (hj : ε j = true) :
    (i : ℤ) < j := by
  by_contra hc
  have hji : j ≤ i := by
    rw [Fin.le_iff_val_le_val]
    omega
  have h3 := hε hji
  rw [hi, hj] at h3
  exact absurd h3 (by decide)
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
