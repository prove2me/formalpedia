-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.ExpansionTerms.n3cModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:14.265711+00:00
-- url     : https://prove2.me/submissions/d316f879-c6f8-4884-94e4-54acb983b91d

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Definitions.Def_Formalism_FlagUnipotentLattices_BlockMinorAbsoluteFromExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_vector_norm_on_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.Final.ExpansionTerms
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.DualVectorNormOnGroup := Formalism.HermitianLatticeCounting.P.dual_vector_norm_on_group
end Formalism.HermitianLatticeCounting.Final.ExpansionTerms
