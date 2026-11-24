-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S6.pairsLoss
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:42.538159+00:00
-- url     : https://prove2.me/submissions/b50db726-1d57-46c6-a857-1994ef23d21e

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_LiftFixesBaseVector
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_pairs_loss_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S6
namespace Formalism.HermitianLatticeCounting.Final.S6
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.PairsLoss := Formalism.HermitianLatticeCounting.P.pairs_loss_bound
end Formalism.HermitianLatticeCounting.Final.S6
