-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.ql_sW_cast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:44:31.112347+00:00
-- url     : https://prove2.me/submissions/03fdde1c-a6bc-45df-88cd-df2f9e71b172

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
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
theorem _root_.solution : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), ((ql_sW ℤ N D : ℤ) : R) = ql_sW R N D
  | 0, _ => by simp [ql_sW]
  | N + 1, D => by simp only [ql_sW, Int.cast_mul, ql_s_cast, solution N]
end Formalism.InvariantFactorPaths.ColumnFamilies
