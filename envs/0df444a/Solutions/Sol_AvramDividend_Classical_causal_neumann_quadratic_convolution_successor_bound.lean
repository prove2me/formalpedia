-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_quadratic_convolution_successor_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:25:55.852013+00:00
-- url     : https://prove2.me/submissions/c831d643-12b3-44e7-9789-5bd3e4c48ef4

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_antitone_convolution_cutoff_split_mass_bound

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The antitone cutoff step propagates a quadratic-geometric pointwise bound. -/
theorem solution
    (n : ℕ) (κ F : ℝ → ℝ) (ρ x u : ℝ)
    (hx : 0 < x) (hρ : 0 ≤ ρ)
    (hcut : u = ((n + 1 : ℝ) / (n + 2 : ℝ)) * x)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hκcutInt : IntervalIntegrable κ volume 0 (x - u))
    (hκcutMass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ)
    (hleftInt : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 u)
    (hrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume u x)
    (hFInt : IntervalIntegrable F volume 0 u)
    (hκrightInt : IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x)
    (hFleft : ∀ s ∈ Ioo (0 : ℝ) u, 0 ≤ F s)
    (hFright : ∀ s ∈ Ioo u x,
      F s ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / s)
    (hκright : ∀ s ∈ Ioo u x, 0 ≤ κ (x - s))
    (hFmass : (∫ s in (0 : ℝ)..u, F s) ≤ ρ ^ (n + 1)) :
    (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤
      ((n + 2 : ℝ) ^ 2 * ρ ^ (n + 2)) / x := by
  have hn1 : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hn2 : (0 : ℝ) < (n + 2 : ℝ) := by positivity
  have hu : 0 < u := by
    rw [hcut]
    exact mul_pos (div_pos hn1 hn2) hx
  have hsep : x - u = x / (n + 2 : ℝ) := by
    rw [hcut]
    field_simp
    ring
  have hxu : 0 < x - u := by
    rw [hsep]
    exact div_pos hx hn2
  have hux : u ≤ x := by linarith
  let A : ℝ := (n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (pow_nonneg hρ _)
  have hB : 0 ≤ A / u := div_nonneg hA hu.le
  have hFrightB : ∀ s ∈ Ioo u x, F s ≤ A / u := by
    intro s hs
    have hspos : 0 < s := lt_trans hu hs.1
    have hdiv : A / s ≤ A / u := by
      apply (div_le_div_iff₀ hspos hu).2
      exact mul_le_mul_of_nonneg_left hs.1.le hA
    exact (hFright s hs).trans hdiv
  have hmain :=
    AvramDividend.Classical.causal_antitone_convolution_cutoff_split_mass_bound
      κ F x u ρ (ρ ^ (n + 1)) (A / u)
      hu.le hux hxu hρ hB hanti hκcutInt hκcutMass
      hleftInt hrightInt hFInt hκrightInt hFleft hFrightB
      hκright hFmass
  have hpow : ρ ^ (n + 2) = ρ ^ (n + 1) * ρ := by
    rw [show n + 2 = (n + 1) + 1 by ring, pow_succ]
  have hstep :
      (ρ / (x - u)) * ρ ^ (n + 1) + (A / u) * ρ =
      ((n + 2 : ℝ) ^ 2 * ρ ^ (n + 2)) / x := by
    rw [hsep, hcut]
    dsimp [A]
    rw [hpow]
    field_simp
    ring
  change (∫ s in (0 : ℝ)..x, κ (x - s) * F s) ≤
    (ρ / (x - u)) * ρ ^ (n + 1) + (A / u) * ρ at hmain
  rw [hstep] at hmain
  exact hmain
