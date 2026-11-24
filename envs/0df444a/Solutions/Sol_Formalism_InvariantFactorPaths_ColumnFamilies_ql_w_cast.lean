-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_w_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:50.670298+00:00
-- url     : https://prove2.me/submissions/c00a35b8-36e2-4caf-a723-a0e2d35bdc15

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_s_cast

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
theorem _root_.solution (A K I : Finset (Fin n)) : ((ql_w ℤ A K I : ℤ) : R) = ql_w R A K I := by
  unfold ql_w; split_ifs
  · exact ql_s_cast A K
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
