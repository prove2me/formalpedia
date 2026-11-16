-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_factorial_series_norm_summable_mean_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:45:53.725914+00:00
-- url     : https://prove2.me/submissions/e58723f6-4b6b-4275-98bc-2dbd9ef6d1fe

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_scaled_factorial_coeff_integrable_mean_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Absolute summability of the physical factorial-moment series. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n)
    (z : ℝ) (hz : 0 ≤ z) :
    let F : ℕ → Ω → ℝ := fun n ω =>
      (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))
    Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂P) ∧
      (∑' n : ℕ, ∫ ω, F n ω ∂P) = Real.exp ((r : ℝ) * z) := by
  let F : ℕ → Ω → ℝ := fun n ω =>
    (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))
  change Summable (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂P) ∧
    (∑' n : ℕ, ∫ ω, F n ω ∂P) = Real.exp ((r : ℝ) * z)
  have hFactor (n : ℕ) :
      Integrable (F n) P ∧
        (∫ ω, F n ω ∂P) = ((r : ℝ) * z) ^ n / (n.factorial : ℝ) :=
    avram_a25_scaled_factorial_coeff_integrable_mean_20261115
      P K r hr hMom z n
  have hNorm (n : ℕ) :
      (∫ ω, ‖F n ω‖ ∂P) = ((r : ℝ) * z) ^ n / (n.factorial : ℝ) := by
    calc
      (∫ ω, ‖F n ω‖ ∂P) = ∫ ω, F n ω ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        apply Real.norm_of_nonneg
        dsimp [F]
        positivity
      _ = _ := (hFactor n).2
  have hs : Summable
      (fun n : ℕ => ((r : ℝ) * z) ^ n / (n.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).summable
  constructor
  · have he : (fun n : ℕ => ∫ ω, ‖F n ω‖ ∂P) =
        (fun n : ℕ => ((r : ℝ) * z) ^ n / (n.factorial : ℝ)) :=
      funext hNorm
    rw [he]
    exact hs
  · calc
      (∑' n : ℕ, ∫ ω, F n ω ∂P) =
          ∑' n : ℕ, ((r : ℝ) * z) ^ n / (n.factorial : ℝ) := by
        apply tsum_congr
        intro n
        exact (hFactor n).2
      _ = Real.exp ((r : ℝ) * z) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * z)).tsum_eq,
          exp_eq_exp_ℝ]
