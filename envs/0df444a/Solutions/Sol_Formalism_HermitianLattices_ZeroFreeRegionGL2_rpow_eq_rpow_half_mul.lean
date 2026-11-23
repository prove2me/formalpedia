-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_eq_rpow_half_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:56.096312+00:00
-- url     : https://prove2.me/submissions/0f334452-a9cb-4cc4-89fc-3f3656f0fe36

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution (x a : ℝ) (hx : 0 < x) : x ^ a = x ^ (a / 2) * x ^ (a / 2) := by
  rw [← Real.rpow_add hx]; congr 1; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
