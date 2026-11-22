-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sum_w
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:12.640877+00:00
-- url     : https://prove2.me/submissions/c4abd789-93af-43d4-812e-2b1142a35eb6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn

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
theorem _root_.solution (A K : Finset (Fin n)) (f : Finset (Fin n) → R) :
    ∑ I, f I * ql_w R A K I = wedgeSign R A K * f (A ∪ K) := by
  simp [ql_w, mul_comm]
end Formalism.InvariantFactorPaths.ColumnFamilies
