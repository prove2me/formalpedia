-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:01.200416+00:00
-- url     : https://prove2.me/submissions/f2e09b4c-d208-498b-a2d6-c787624d6975

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : Fin (r + 1) → ℂ)
    (hZ : Zhat k r z z' g = diagonal d) (l : Fin (r + 2)) :
    Dmin k r z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Dmin
  rw [hZ, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
  rfl
end Formalism.QuantumDeterminants.BruhatBigCell
