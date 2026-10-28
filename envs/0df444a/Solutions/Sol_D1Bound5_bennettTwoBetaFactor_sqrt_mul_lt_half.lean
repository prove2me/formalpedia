-- Prove2me | solution 1 for D1Bound5.bennettTwoBetaFactor_sqrt_mul_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:24:27.005823+00:00
-- url     : https://prove2.me/submissions/066cb919-3944-4ee6-a9fe-11c7ce4b0d43

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
import Theorems.Thm_D1Bound5_bennettTwoBetaFactor_le
import Theorems.Thm_D1Bound5_bennettTwoBetaFactor_pos

section
namespace D1Bound5



















/-- The normalized residual bound is strictly below one half once the exact
beta expression has been derived; no estimate of a recurrence is assumed. -/
theorem _root_.solution
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt η * bennettTwoBetaFactor k < 1 / 2 := by
  have hs : Real.sqrt η ≤ 1 := by
    nlinarith [Real.sq_sqrt hη0, Real.sqrt_nonneg η]
  calc
    _ ≤ 1 * bennettTwoBetaFactor k :=
      mul_le_mul_of_nonneg_right hs (bennettTwoBetaFactor_pos k hk).le
    _ = bennettTwoBetaFactor k := one_mul _
    _ ≤ 27 / 64 := bennettTwoBetaFactor_le k hk
    _ < 1 / 2 := by norm_num

end D1Bound5
end
