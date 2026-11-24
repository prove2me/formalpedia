-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_domLE_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:15.380792+00:00
-- url     : https://prove2.me/submissions/f56f13d7-c1c7-49ef-95f4-8ddd3c696d3a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_psi_le
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_eq_of_psi

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {nu mu : Fin n → ℤ} (h1 : DomLE nu mu) (h2 : DomLE mu nu) : nu = mu :=
  qb_eq_of_psi h1 (qb_psi_le h2)
end Formalism.InvariantFactorPaths.ColumnFamilies
