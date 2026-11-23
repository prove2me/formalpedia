-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.four_le_four_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:40.018426+00:00
-- url     : https://prove2.me/submissions/21947002-81ad-4155-82be-93d2dde6599e

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
theorem _root_.solution (d N : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N) : 4 ≤ 4 * d * N ^ 2 := by
  have h1 : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have h2 : 1 ≤ d * N ^ 2 := one_le_mul_of_one_le_of_one_le hd h1
  linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
