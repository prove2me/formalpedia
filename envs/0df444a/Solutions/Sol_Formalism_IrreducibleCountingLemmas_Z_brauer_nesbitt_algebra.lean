-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:47.719482+00:00
-- url     : https://prove2.me/submissions/3ddb1e7f-90bc-4f04-b8e5-b99f79f93c4c

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_mul_eq_one_of_covolume_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : BrauerNesbittAlg := by
  intro k A V W _ _ _ _ _ _ _ _ _ _ _ _ _ hV hW h
  exact BN.mul_eq_one_of_covolume_identity _ V W rfl hV hW h
end Formalism.IrreducibleCountingLemmas.Z
