-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_natural_inner_clock_delta_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:39:16.226313+00:00
-- url     : https://prove2.me/submissions/0425a3a6-aff4-4a08-b78d-3532956f479e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology
noncomputable section

/-- Exact cofinal strict natural clocks used by the original stopped BV grid. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    (∀ n, 0 < δ n) ∧ (∀ n, δ n ≤ T) ∧
      Antitone δ ∧ Tendsto δ atTop (𝓝 0) := by
  dsimp
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    apply tendsto_atTop.2
    intro b
    filter_upwards [hcast.eventually (eventually_ge_atTop b)] with n hn
    linarith
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hden
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact div_pos hT (by positivity)
  · intro n
    calc
      T / ((n : ℝ) + 2) ≤ T / 1 :=
        div_le_div_of_nonneg_left (le_of_lt hT) (by norm_num) (by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
      _ = T := by ring
  · intro a b hab
    exact div_le_div_of_nonneg_left (le_of_lt hT)
      (by positivity) (by exact_mod_cast (Nat.add_le_add_right hab 2))
  · simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv)
