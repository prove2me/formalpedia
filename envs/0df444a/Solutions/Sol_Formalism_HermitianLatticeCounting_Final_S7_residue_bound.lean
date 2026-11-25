-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.S7.residue_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:31:41.192804+00:00
-- url     : https://prove2.me/submissions/06935a2f-70d5-49c2-bf10-4f3b50dc01f5

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoveringOfTransferenceVariant
import Definitions.Def_Formalism_FlagUnipotentLattices_FinalTr
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dedekindZeta_residue_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.S7
namespace Formalism.HermitianLatticeCounting.Final.S7
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.DedekindZetaResidueBound := Formalism.HermitianLatticeCounting.P.dedekindZeta_residue_bound
end Formalism.HermitianLatticeCounting.Final.S7
