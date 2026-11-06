-- Prove2me | solution 1 for BianchiIX.reciprocal_radial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:51.958799+00:00
-- url     : https://prove2.me/submissions/4949b9fd-a1d0-47f0-9e83-f55bd188cce7

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- A positive phase with positive radial slope gives a decreasing reciprocal radius. -/
theorem solution {f : ℝ → ℝ} {x r B M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hf : DifferentiableAt ℝ f x)
    (hlo : r / 16 ≤ f x) (hhi : f x ≤ B * r)
    (hdlo : 1 / 8 ≤ deriv f x) (hdhi : deriv f x ≤ M) :
    DifferentiableAt ℝ (fun y => 2 / f y) x ∧
      2 / (B * r) ≤ 2 / f x ∧ 2 / f x ≤ 32 / r ∧
      1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv (fun y => 2 / f y) x ∧
      -deriv (fun y => 2 / f y) x ≤ 512 * M / r ^ 2 := by
  have hfpos : 0 < f x := lt_of_lt_of_le (by positivity : 0 < r / 16) hlo
  have hne := ne_of_gt hfpos
  have HD := (differentiableAt_const (2 : ℝ)).div hf hne
  have Hder : -deriv (fun y => 2 / f y) x = 2 * deriv f x / (f x) ^ 2 := by
    rw [deriv_const_div 2 hf hne]
    ring
  refine ⟨HD, ?_, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (by norm_num) hfpos hhi
  · calc
      _ ≤ 2 / (r / 16) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo
      _ = 32 / r := by ring
  · rw [Hder]
    calc
      _ = ((1 : ℝ) / 4) / (B * r) ^ 2 := by ring
      _ ≤ ((1 : ℝ) / 4) / (f x) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hfpos)
          (pow_le_pow_left₀ hfpos.le hhi 2)
      _ ≤ 2 * deriv f x / (f x) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith only [hdlo]) (sq_nonneg _)
  · rw [Hder]
    calc
      _ ≤ 2 * M / (f x) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith only [hdhi]) (sq_nonneg _)
      _ ≤ 2 * M / (r / 16) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) hlo 2)
      _ = 512 * M / r ^ 2 := by ring
