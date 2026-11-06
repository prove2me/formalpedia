-- Prove2me | solution 1 for BianchiIX.entrance_phase_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:44:39.761292+00:00
-- url     : https://prove2.me/submissions/8cfd5559-06dc-428f-813a-7e8d38a0ada6

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

theorem solution {k m v : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100) (hv : 0 ≤ v ∧ v ≤ 1) :
    4 / 5 * k ≤ m - 1 ∧ m - 1 ≤ 101 / 100 * k := by
  have hk0 : 0 ≤ k := by linarith
  have hR0 : 0 ≤ coreRadius m v := Real.sqrt_nonneg _
  obtain ⟨hRlo, hRhi⟩ := abs_le.mp hr
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  have hv2 : v ^ 2 ≤ 1 := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hR2 := mul_nonneg (show 0 ≤ coreRadius m v - 99 / 100 * k by linarith)
    (show 0 ≤ coreRadius m v + 99 / 100 * k by positivity)
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k + 7 / 4 by linarith)
  constructor
  · by_contra h
    have h' : m - 1 < 4 / 5 * k := lt_of_not_ge h
    have hs := mul_nonneg (sub_nonneg.mpr h'.le) (show 0 ≤ 4 / 5 * k + (m - 1) by linarith)
    nlinarith only [he, hR2, hk2, hv2, hs]
  · have ht : m - 1 ≤ coreRadius m v := by
      nlinarith only [he, sq_nonneg v, hR0, hm]
    linarith only [ht, hRhi]
