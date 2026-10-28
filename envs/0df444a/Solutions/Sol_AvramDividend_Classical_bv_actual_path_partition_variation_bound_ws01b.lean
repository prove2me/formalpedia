-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_path_partition_variation_bound_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:05:27.486496+00:00
-- url     : https://prove2.me/submissions/5faeb352-9433-45cb-8d23-ead7dd007268

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/--
For a standing bounded-variation Levy process, every finite increasing
time partition has total path variation bounded by twice the physical
drift contribution minus its terminal increment.

This is the actual (possibly infinite-activity) Levy process, not a
finite-activity approximation. No stochastic Ito formula is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |X.X (u (i + 1)) ω - X.X (u i) ω|) ≤
        2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
          (X.X (u n) ω - X.X (u 0) ω) := by
  have hd : 0 < X.drift :=
    (bv_standing_drift_pos X hX hBV).1
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hres
  intro u hu n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have htime : (u n : ℝ) ≤ (u (n + 1) : ℝ) := by
        exact_mod_cast hu (Nat.le_succ n)
      have hstep_time :
          0 ≤ (u (n + 1) : ℝ) - (u n : ℝ) :=
        sub_nonneg.mpr htime
      have hdelta :
          X.X (u (n + 1)) ω - X.X (u n) ω ≤
            X.drift * ((u (n + 1) : ℝ) - (u n : ℝ)) := by
        have hs := hres (hu (Nat.le_succ n))
        dsimp at hs
        nlinarith
      have hstep :
          |X.X (u (n + 1)) ω - X.X (u n) ω| ≤
            2 * X.drift * ((u (n + 1) : ℝ) - (u n : ℝ)) -
              (X.X (u (n + 1)) ω - X.X (u n) ω) := by
        rcases le_total (0 : ℝ)
          (X.X (u (n + 1)) ω - X.X (u n) ω) with hs | hs
        · rw [abs_of_nonneg hs]
          nlinarith
        · rw [abs_of_nonpos hs]
          nlinarith [mul_nonneg (le_of_lt hd) hstep_time]
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range n,
          |X.X (u (i + 1)) ω - X.X (u i) ω|) +
          |X.X (u (n + 1)) ω - X.X (u n) ω|
            ≤
            (2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
              (X.X (u n) ω - X.X (u 0) ω)) +
              (2 * X.drift * ((u (n + 1) : ℝ) - (u n : ℝ)) -
                (X.X (u (n + 1)) ω - X.X (u n) ω)) := by
                  exact add_le_add ih hstep
        _ = 2 * X.drift * ((u (n + 1) : ℝ) - (u 0 : ℝ)) -
              (X.X (u (n + 1)) ω - X.X (u 0) ω) := by ring
