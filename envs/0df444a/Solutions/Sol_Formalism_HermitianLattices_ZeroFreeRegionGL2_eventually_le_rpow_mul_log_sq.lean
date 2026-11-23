-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_le_rpow_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:12.34254+00:00
-- url     : https://prove2.me/submissions/9dcf52cf-3a1a-469b-be1a-866ab41078c6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow

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
theorem _root_.solution (ε K : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
  filter_upwards [eventually_le_rpow (ε / 5) |K| (by positivity), eventually_ge_atTop (Real.exp 1)] with x h h1x
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) h1x
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr h1x
  have hl2 : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hl
  calc K ≤ |K| := le_abs_self K
    _ = |K| * 1 := (mul_one _).symm
    _ ≤ x ^ (ε / 5) * Real.log x ^ 2 := mul_le_mul h hl2 zero_le_one (le_trans (abs_nonneg K) h)
end Formalism.HermitianLattices.ZeroFreeRegionGL2
