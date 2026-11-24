-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_W_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:24.371448+00:00
-- url     : https://prove2.me/submissions/307dc025-9e48-4fd2-9023-753a3b7dc1e9

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_sW_cast

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
theorem _root_.solution {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) :
    ((wedgeCoeff ℤ D L : ℤ) : R) = wedgeCoeff R D L := by
  unfold wedgeCoeff; split_ifs
  · exact ql_sW_cast N D
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
