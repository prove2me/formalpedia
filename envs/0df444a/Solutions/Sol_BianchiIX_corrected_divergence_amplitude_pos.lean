-- Prove2me | solution 1 for BianchiIX.corrected_divergence_amplitude_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:59.617272+00:00
-- url     : https://prove2.me/submissions/e71ab78f-f309-4e64-903b-16e0c82a8e93

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Theorems.Thm_BianchiIX_corrected_divergence_lower_bound
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section

private theorem BianchiIX.corrected_divergence_pos
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) :
    0 < correctedDivergence (curvature a b c) (r ^ 2) := by
  have h := corrected_divergence_lower_bound ha hb hc hr
  exact h.1.trans_le h.2

private theorem BianchiIX.wallAmplitude_eq_square
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    wallAmplitude a b c = ((a * b * c) ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos ha hb) hc).le]
  norm_num [wallAmplitude]

theorem solution
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < correctedDivergence (curvature a b c) (wallAmplitude a b c) := by
  rw [wallAmplitude_eq_square ha hb hc]
  apply corrected_divergence_pos ha hb hc
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos ha hb) hc).le]
  norm_num
