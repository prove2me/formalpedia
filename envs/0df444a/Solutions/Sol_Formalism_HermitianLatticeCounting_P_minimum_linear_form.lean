-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minimum_linear_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:40.483678+00:00
-- url     : https://prove2.me/submissions/31be1347-0553-4440-ad97-752ca64ddc13

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : MinLinear := by
  intro q ε s hq hε h1 hs
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hs0 : 0 < Real.sqrt (2 * (q:ℝ)) := Real.sqrt_pos.mpr (by linarith)
  refine le_min (by nlinarith) ?_
  rw [le_div_iff₀ hs0]
  have : 0 < s := by linarith
  nlinarith
end Formalism.HermitianLatticeCounting.P
