-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.sizes_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:49:26.925494+00:00
-- url     : https://prove2.me/submissions/e8a9027b-b541-4677-b355-878c40c8cb43

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_sizesProduct_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.SizesProduct :=
  Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok
end Formalism.FourierDecayAlt.P
