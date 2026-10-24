-- Prove2me | solution 1 for AvramDividend.Classical.positive_ramp_cutoff_continuous_and_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:26:46.057048+00:00
-- url     : https://prove2.me/submissions/1b5a7487-8a6b-4232-9d34-f80fdb48cb49

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The clipped affine ramp is continuous and interpolates between zero and one. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε))) ∧
    (∀ x : ℝ, x ≤ ε → max (0 : ℝ) (min 1 ((x - ε) / ε)) = 0) ∧
    (∀ x : ℝ, 2 * ε ≤ x → max (0 : ℝ) (min 1 ((x - ε) / ε)) = 1) := by
  constructor
  · fun_prop
  constructor
  · intro x hx
    have hz : (x - ε) / ε ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le
    exact max_eq_left ((min_le_right (1 : ℝ) ((x - ε) / ε)).trans hz)
  · intro x hx
    have hz : (1 : ℝ) ≤ (x - ε) / ε :=
      (le_div_iff₀ hε).2 (by linarith)
    rw [min_eq_left hz]
    norm_num
