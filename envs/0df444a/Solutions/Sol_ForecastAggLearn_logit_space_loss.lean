-- Prove2me | solution 1 for ForecastAggLearn.logit_space_loss
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:41:38.327992+00:00
-- url     : https://prove2.me/submissions/26689733-1fcb-4643-a721-5a1831711820

import Definitions.Def_ForecastAggLearn_logLoss
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open ForecastAggLearn

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (rt : ℝ) :
    -q * Real.log (1 / (1 + Real.exp (-rt))) -
          (1 - q) * Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) =
        -q * rt - Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) ∧
      -q * rt - Real.log (Real.exp (-rt) / (1 + Real.exp (-rt))) =
        -(q - 1) * rt + Real.log (1 + Real.exp (-rt)) ∧
      ENNReal.ofReal q * logLoss (1 / (1 + Real.exp (-rt))) true +
          ENNReal.ofReal (1 - q) * logLoss (1 / (1 + Real.exp (-rt))) false =
        ENNReal.ofReal (-(q - 1) * rt + Real.log (1 + Real.exp (-rt))) := by
  let e := Real.exp (-rt)
  let d := 1 + e
  let p := 1 / d
  let z := e / d
  have he : 0 < e := Real.exp_pos _
  have hd : 0 < d := by dsimp [d]; linarith
  have hp0 : 0 < p := div_pos zero_lt_one hd
  have hp1 : p < 1 := by
    apply (div_lt_iff₀ hd).mpr
    dsimp [d]
    linarith
  have hcomp : 1 - p = z := by
    dsimp only [p, z]
    field_simp [ne_of_gt hd]
    dsimp [d]
    ring
  have hlogp : Real.log p = -Real.log d := by
    change Real.log (1 / d) = _
    rw [Real.log_div one_ne_zero hd.ne', Real.log_one, zero_sub]
  have hlogz : Real.log z = -rt - Real.log d := by
    change Real.log (e / d) = _
    rw [Real.log_div he.ne' hd.ne']
    exact congrArg (fun x => x - Real.log d) (Real.log_exp (-rt))
  change (-q * Real.log p - (1 - q) * Real.log z = -q * rt - Real.log z) ∧
    (-q * rt - Real.log z = -(q - 1) * rt + Real.log d) ∧
    (ENNReal.ofReal q * logLoss p true + ENNReal.ofReal (1 - q) * logLoss p false =
      ENNReal.ofReal (-(q - 1) * rt + Real.log d))
  refine ⟨?_, ?_, ?_⟩
  · rw [hlogp, hlogz]
    ring
  · rw [hlogz]
    ring
  · have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq1
    have hnp : 0 ≤ -Real.log p := neg_nonneg.mpr (Real.log_nonpos hp0.le hp1.le)
    have hnz : 0 ≤ -Real.log z := by
      rw [← hcomp]
      exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr hp1.le) (by linarith))
    simp [logLoss, not_le.mpr hp0, not_le.mpr hp1, hcomp]
    rw [← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul hq',
      ← ENNReal.ofReal_add (mul_nonneg hq0 hnp) (mul_nonneg hq' hnz)]
    congr 1
    rw [hlogp, hlogz]
    ring

#print axioms solution
