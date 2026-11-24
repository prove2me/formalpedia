-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.gram_expansion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:10.122022+00:00
-- url     : https://prove2.me/submissions/8b71f523-afc6-46a5-bade-b75986fd8eb1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Theorems.Thm_Formalism_HermitianLattices_WeilRepresentation_CocycleEighthPower_rv_gram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation
namespace Formalism.HermitianLattices.WeilRepresentation
theorem _root_.solution : GramExpansion := CocycleEighthPower.rv_gram
end Formalism.HermitianLattices.WeilRepresentation
