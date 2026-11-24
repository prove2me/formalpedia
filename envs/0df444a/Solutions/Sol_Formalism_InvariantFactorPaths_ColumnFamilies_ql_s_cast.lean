-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_s_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:04.817612+00:00
-- url     : https://prove2.me/submissions/3bb27841-d975-460e-9fe9-22e94160a86c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sr_cast

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
theorem _root_.solution (A K : Finset (Fin n)) : ((wedgeSign ℤ A K : ℤ) : R) = wedgeSign R A K := by
  unfold wedgeSign; split_ifs
  · exact ql_sr_cast A K
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
