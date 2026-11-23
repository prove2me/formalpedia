-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_mul_log_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.9558+00:00
-- url     : https://prove2.me/submissions/57ef1aaf-27a0-41e6-932d-f54183ddceb2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_rpow_eq_rpow_half_mul

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
theorem _root_.solution (a K : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K * Real.log x ≤ x ^ a := by
  have h1 := eventually_le_rpow (a / 2) (|K| * (2 / a)) (by positivity)
  filter_upwards [h1, eventually_ge_atTop 1] with x hx h1x
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≤ x ^ (a / 2) / (a / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg h1x
  have hp : 0 < x ^ (a / 2) := Real.rpow_pos_of_pos hx0 _
  calc K * Real.log x ≤ |K| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self K) hl0
    _ ≤ |K| * (x ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left hl (abs_nonneg K)
    _ = (|K| * (2 / a)) * x ^ (a / 2) := by field_simp
    _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right hx hp.le
    _ = x ^ a := (rpow_eq_rpow_half_mul x a hx0).symm
end Formalism.HermitianLattices.ZeroFreeRegionGL2
