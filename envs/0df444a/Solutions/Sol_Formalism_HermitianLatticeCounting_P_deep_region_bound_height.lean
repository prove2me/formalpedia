-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.deep_region_bound_height
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:32.957989+00:00
-- url     : https://prove2.me/submissions/09a2f57b-e01f-4a1c-bc3d-157eff947ce8

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
theorem _root_.solution : DeepBoundY := by
  intro C hC
  refine ⟨2 * C + 2, by linarith, ?_⟩
  intro n q f Y hq hY
  have hY0 : 0 < Y := by linarith
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  rw [← Real.rpow_mul_natCast hY0.le, ← Real.rpow_add hY0, Real.rpow_def_of_pos hY0]
  apply Real.exp_le_exp.mpr
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hm0 : 0 ≤ (n:ℝ) ^ 2 * f := by positivity
  have hE : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f
      + -((2 * C + 2) * q) * ((12 * n ^ 2 * f : ℕ) : ℝ) ≤ -2 * ((n:ℝ) ^ 2 * f) := by
    push_cast
    have : (16 * q * C + 2 * C + 16) * (n:ℝ) ^ 2 * f + -((2 * C + 2) * q) * (12 * (n:ℝ) ^ 2 * f)
        = (-(8 * q * C) + 2 * C + 16 - 24 * q) * ((n:ℝ) ^ 2 * f) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ hm0
    nlinarith
  nlinarith
end Formalism.HermitianLatticeCounting.P
