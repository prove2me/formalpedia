-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_W_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:25.126256+00:00
-- url     : https://prove2.me/submissions/938881fa-8c50-4f6c-8fd3-bb5d6ed93991

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {N : ℕ} (D : Fin (N + 1) → Finset (Fin n)) (L : Finset (Fin n)) :
    wedgeCoeff R D L = ∑ M, ql_w R (D 0) M L * wedgeCoeff R (Fin.tail D) M := by
  simp only [wedgeCoeff, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, ql_U, ql_sW, ql_w, ite_mul, zero_mul]
  congr
end Formalism.InvariantFactorPaths.ColumnFamilies
