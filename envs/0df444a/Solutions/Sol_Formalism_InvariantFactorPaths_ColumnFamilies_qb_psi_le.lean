-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_psi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:42.806394+00:00
-- url     : https://prove2.me/submissions/47dfd742-44ec-4b19-97cc-56f8f6dc8ff5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW

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
theorem _root_.solution {nu mu : Fin n → ℤ} (h : DomLE nu mu) : qb_psi nu ≤ qb_psi mu :=
  sum_le_sum fun a _ => h.1 a
end Formalism.InvariantFactorPaths.ColumnFamilies
