-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_log_sq_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:48.665915+00:00
-- url     : https://prove2.me/submissions/757cca03-b9b0-45a0-aba7-ea4531fb259f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_rpow_eq_rpow_half_mul
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_mul_log_le_rpow

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
theorem _root_.solution (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K * Real.log x ^ 2 ≤ x ^ a := by
  filter_upwards [eventually_mul_log_le_rpow (a / 2) |K| (by positivity), eventually_mul_log_le_rpow (a / 2) 1 (by positivity),
    eventually_ge_atTop 1] with x h1 h2 h1x
  have hx0 : 0 < x := by linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1x
  have hp : 0 < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  calc K * Real.log x ^ 2 ≤ |K| * Real.log x ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
    _ = (|K| * Real.log x) * (1 * Real.log x) := by ring
    _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul h1 h2 (by positivity) hp.le
    _ = x ^ a := (rpow_eq_rpow_half_mul x a hx0).symm
end Formalism.HermitianLattices.ZeroFreeRegionGL2
