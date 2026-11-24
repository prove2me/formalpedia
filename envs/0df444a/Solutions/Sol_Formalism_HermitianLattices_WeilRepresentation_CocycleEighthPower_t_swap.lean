-- Prove2me | solution 1 for Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower.t_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:48.645824+00:00
-- url     : https://prove2.me/submissions/8b3f84ea-5286-4343-a9f8-30516dc5acf6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareEqDiagOfQuadraticEven

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
open Formalism.HermitianLattices.WeilRepresentation Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
theorem _root_.solution : ModelCocycleTwoSwapped := by
  intro δ a b h; field_simp; ring
end Formalism.HermitianLattices.WeilRepresentation.CocycleEighthPower
