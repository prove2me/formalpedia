-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp16_diagonal_vanishing_error_of_fixed_band_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:52:55.490688+00:00
-- url     : https://prove2.me/submissions/764a2eb7-e77e-4cc5-80e6-94bcfbcaa9d5

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_cofinal_safe_diagonal_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
noncomputable section

theorem solution
    (N : ℕ → ℕ) (hN0 : N 0 = 0)
    (hNge : ∀ k, k ≤ N k)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (Err : ℕ → ℕ → ℝ)
    (hErr : ∀ k n, 0 < k → N k ≤ n → |Err k n| ≤ |ε k|) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      (∀ n, N (κ n) ≤ n) ∧
      Tendsto κ atTop atTop ∧
      Tendsto (fun n => Err (κ n) n) atTop (nhds 0) := by
  obtain ⟨κ, hκle, hκsafe, hκtop⟩ :=
    AvramDividend.Classical.avram_p3_comp16_cofinal_safe_diagonal_schedule
      N hN0 hNge
  refine ⟨κ, hκle, hκsafe, hκtop, ?_⟩
  have hlim : Tendsto (fun n => |ε (κ n)|) atTop (nhds (0 : ℝ)) := by
    simpa using (hε.comp hκtop).abs
  apply squeeze_zero_norm' (a := fun n => |ε (κ n)|)
  · filter_upwards [(Filter.tendsto_atTop.1 hκtop 1)] with n hn
    rw [Real.norm_eq_abs]
    exact hErr (κ n) n (by omega) (hκsafe n)
  · exact hlim
