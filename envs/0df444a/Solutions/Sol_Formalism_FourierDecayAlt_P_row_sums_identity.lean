-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.row_sums_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:53:12.065386+00:00
-- url     : https://prove2.me/submissions/74c035cf-9d49-4163-b5a5-a971b0fe6c52

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_rowSums_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.RowSums := Formalism.FourierDecayAlt.P.ChainAndRowSums.rowSums_ok
end Formalism.FourierDecayAlt.P
