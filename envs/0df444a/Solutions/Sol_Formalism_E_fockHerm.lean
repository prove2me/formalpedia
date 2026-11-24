-- Prove2me | solution 1 for Formalism.E.fockHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:27:20.126071+00:00
-- url     : https://prove2.me/submissions/bad43761-7e29-48fc-844f-2261a0287226

import Definitions.Def_Formalism_FockGram_FockGramProofs_FockHerm
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockSesq
import Definitions.Def_Formalism_FockGram_FockGramProofs_FockPerm
import Definitions.Def_Formalism_FockGram_FockGramProofs_DetSymPow
import Definitions.Def_Formalism_FockGram_FockGramProofs_SubIndexNorm
import Mathlib
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermDualOf
import Definitions.Def_Formalism_FockGram_FockGramProofs_HermitianTensorMulHermitian
import Definitions.Def_Formalism_FockGram_StatementSymPos
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Theorems.Thm_Formalism_E_fischerInnerConjSymm_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.E
namespace Formalism.E
theorem _root_.solution : FockHerm := fischerInnerConjSymm_holds
end Formalism.E
