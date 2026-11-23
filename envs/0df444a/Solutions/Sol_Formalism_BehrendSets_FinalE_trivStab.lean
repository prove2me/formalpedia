-- Prove2me | solution 1 for Formalism.BehrendSets.FinalE.trivStab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:46.265446+00:00
-- url     : https://prove2.me/submissions/7b57c5c9-f409-4bb4-af8a-aad477e2cbd8

import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoPowDvdPowTwoPowSubOne
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_SpaceFreeOfBehrendFree
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MemWindowIff
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProdDimVNeZero
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_CoeffPowEqZeroOfLt
import Definitions.Def_Formalism_BehrendSets_FinalE
import Theorems.Thm_Formalism_BehrendSets_trivStab


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BehrendSets Formalism.BehrendSets.FinalE
open Formalism.BehrendSets
namespace Formalism.BehrendSets.FinalE
theorem _root_.solution : TrivStab := Formalism.BehrendSets.trivStab
end Formalism.BehrendSets.FinalE
