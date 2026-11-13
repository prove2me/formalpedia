-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a26_terminal_spatial_zero_after_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:11:23.748963+00:00
-- url     : https://prove2.me/submissions/792527f5-1948-4c1a-879d-b25d699e4077

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution {Ω : Type*}
    (L D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (x : ℝ)
    (n : ℝ≥0) (m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hstop : ρ ω ≤ (m : ℝ≥0) * (n / ((m : ℝ≥0) + 1))) :
    let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    w (x + L (v (m + 1)) ω - D (v m) ω) -
      w (x + L (v m) ω - D (v m) ω) = 0 := by
  let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
  have hcast : (m : ℝ≥0) ≤ ((m + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ m
  have hgrid : (m : ℝ≥0) * Δ ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right hcast (by positivity)
  have hm : min ((m : ℝ≥0) * Δ) (ρ ω) = ρ ω := min_eq_right hstop
  have hn : min (((m + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω) = ρ ω :=
    min_eq_right (hstop.trans hgrid)
  change w (x + L (min (((m + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)) ω -
      D (min ((m : ℝ≥0) * Δ) (ρ ω)) ω) -
    w (x + L (min ((m : ℝ≥0) * Δ) (ρ ω)) ω -
      D (min ((m : ℝ≥0) * Δ) (ρ ω)) ω) = 0
  simp only [hm, hn, sub_self]
