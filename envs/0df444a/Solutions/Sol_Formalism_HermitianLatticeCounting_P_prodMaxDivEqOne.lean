-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodMaxDivEqOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:59.239212+00:00
-- url     : https://prove2.me/submissions/d93bbc8c-958f-479a-bd38-30fceb6e700a

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ThresholdBelow := by
  intro N D H₂ hH hD
  exact Finset.prod_eq_one (fun i _ => max_eq_left ((div_le_one hH).mpr (hD i)))
end Formalism.HermitianLatticeCounting.P
