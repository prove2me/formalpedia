-- Prove2me | solution 1 for Formalism.E.subIndexNorm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:40.369407+00:00
-- url     : https://prove2.me/submissions/32b09482-ddc5-48d7-89aa-c77e0d9e2fba

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
import Theorems.Thm_Formalism_E_indexEqNormDet


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
theorem _root_.solution : SubIndexNorm := indexEqNormDet
end Formalism.E
