-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.heisenberg_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:52.905641+00:00
-- url     : https://prove2.me/submissions/ec94a906-2138-4f53-bfc9-bd1007767564

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven
import Theorems.Thm_Formalism_HermitianLattices_WeilRepresentation_CocycleEighthPower_t_heis

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
theorem _root_.solution : HeisenbergCocycle := CocycleEighthPower.t_heis
end Formalism.HermitianLattices.WeilRepresentation
