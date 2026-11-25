-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.model_cocycle_two_swapped
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:07:20.764503+00:00
-- url     : https://prove2.me/submissions/fd7f6199-a755-495f-a1b6-13ed8f35e5a0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Theorems.Thm_Formalism_HermitianLattices_WeilRepresentation_CocycleEighthPower_t_swap

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
theorem _root_.solution : ModelCocycleTwoSwapped := CocycleEighthPower.t_swap
end Formalism.HermitianLattices.WeilRepresentation
