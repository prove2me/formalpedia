-- Prove2me | solution 2 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_mul_rpow_log_sq_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.814875+00:00
-- url     : https://prove2.me/submissions/c8cf4e64-555d-4a02-b851-c4940d545694

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_log_sq_le_rpow

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
theorem _root_.solution (ε M : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, M * (x ^ (ε / 5) * Real.log x ^ 2) ≤ x ^ ε := by
  filter_upwards [eventually_log_sq_le_rpow (4 * ε / 5) M (by positivity), eventually_ge_atTop 1] with x h h1x
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ ε = x ^ (ε / 5) * x ^ (4 * ε / 5) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hp : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
  calc M * (x ^ (ε / 5) * Real.log x ^ 2) = x ^ (ε / 5) * (M * Real.log x ^ 2) := by ring
    _ ≤ x ^ (ε / 5) * x ^ (4 * ε / 5) := mul_le_mul_of_nonneg_left h hp.le
    _ = x ^ ε := hsplit.symm
end Formalism.HermitianLattices.ZeroFreeRegionGL2
