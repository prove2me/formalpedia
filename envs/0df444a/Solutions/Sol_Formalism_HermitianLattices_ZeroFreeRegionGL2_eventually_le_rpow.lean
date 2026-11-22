-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:35.594919+00:00
-- url     : https://prove2.me/submissions/a115cc89-d797-44a1-b3ee-2b87eb5547c3

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
theorem _root_.solution (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a :=
  (tendsto_rpow_atTop ha).eventually_ge_atTop K
end Formalism.HermitianLattices.ZeroFreeRegionGL2
