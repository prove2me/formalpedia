-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.normSymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:35.647823+00:00
-- url     : https://prove2.me/submissions/e4b1e28e-a4a7-4a41-91ef-a59349e71cb8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (a b : Fin N) :
    ‖X a b‖ ^ 2 = ‖X b a‖ ^ 2 := by
  rw [← hX.apply a b, norm_star]
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
