-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_dMu_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:23.681617+00:00
-- url     : https://prove2.me/submissions/4156bdb7-619f-4f07-83cf-b73d59da99da

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_idxE_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) : dMu (qc_sh mu ε) = dMu mu :=
  Nat.card_congr ((qc_idxE mu ε).subtypeEquiv (qc_idxE_std mu ε))
end Formalism.InvariantFactorPaths.ColumnFamilies
