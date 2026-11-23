-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.log_four_mul_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:40.483489+00:00
-- url     : https://prove2.me/submissions/fd50e8ca-ee8f-4c62-98b8-1840a9b3bf6c

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
theorem _root_.solution (d N : ℝ) (hd : 0 < d) (hN : 0 < N) :
    Real.log (4 * d * N ^ 2) = Real.log 4 + Real.log d + 2 * Real.log N := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
