-- Prove2me | solution 1 for AvramDividend.Classical.chat03_killed_scale_grid_optional_stopping_of_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:31:33.558698+00:00
-- url     : https://prove2.me/submissions/76042447-3d04-4825-b04f-926c77331b0a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex_exists
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-!
Actual killed q-scale payoff at the bounded sampled two-sided exit.
The independently required killed-martingale premise is explicit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hx : 0 ≤ x)
    (hKilled : Martingale
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) 𝓕 P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) →
          0 ≤ x + X.X s ω}).indicator
      (fun ω =>
        Real.exp (-(q * (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) : ℝ))) *
        W (x + X.X (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω ∂P) = W x := by
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) ω
  have hM : Martingale M 𝓕 P := hKilled
  obtain ⟨H, hH, hMG⟩ :=
    chat03_martingale_monotone_clock_reindex_exists M hM clock hc
  have hZG : Adapted H (fun k ω => X.X (clock k) ω) := by
    intro k
    rw [hH k]
    exact X.adapted (clock k)
  have hOS := chat03_two_sided_grid_stopped_martingale_identity
    (fun k ω => X.X (clock k) ω)
    (fun k ω => M (clock k) ω)
    hZG hMG lower upper m
  have hM0 : ∀ ω, M (clock 0) ω = W x := by
    intro ω
    simp [M, hclock0, X.X_zero, hx]
  have hInit : (∫ ω, M (clock 0) ω ∂P) = W x := by
    simp_rw [hM0]
    simp
  exact (show (∫ ω, M (clock (hittingBtwn
    (fun k ω => max (X.X (clock k) ω - upper)
      (lower - X.X (clock k) ω))
    (Set.Ioi (0 : ℝ)) 0 m ω)) ω ∂P) = W x from hOS.trans hInit)
