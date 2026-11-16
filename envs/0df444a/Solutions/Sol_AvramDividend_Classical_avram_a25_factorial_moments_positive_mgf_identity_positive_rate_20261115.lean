-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_factorial_moments_positive_mgf_identity_positive_rate_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:52:58.678932+00:00
-- url     : https://prove2.me/submissions/3c86664e-a4e6-40f2-9d6c-54e32e42eb6a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_scaled_factorial_coeff_integrable_mean_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_factorial_series_norm_summable_mean_20261115
import Theorems.Thm_AvramDividend_Classical_avram_a25_nat_factorial_exp_tsum_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- The exponential count MGF from absolutely summable factorial moments. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hr : 0 < r)
    (hMom : ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) = (r : ℝ) ^ n) :
    ∀ θ : ℝ, 0 < θ →
      Integrable (fun ω => Real.exp (θ * (K ω : ℝ))) P ∧
      (∫ ω, Real.exp (θ * (K ω : ℝ)) ∂P) =
        Real.exp ((r : ℝ) * (Real.exp θ - 1)) := by
  intro θ hθ
  let z : ℝ := Real.exp θ - 1
  have hz : 0 ≤ z := by
    dsimp [z]
    nlinarith [Real.add_one_le_exp θ]
  let F : ℕ → Ω → ℝ := fun n ω =>
    (Nat.descFactorial (K ω) n : ℝ) * (z ^ n / (n.factorial : ℝ))
  have hFInt (n : ℕ) : Integrable (F n) P :=
    (avram_a25_scaled_factorial_coeff_integrable_mean_20261115
      P K r hr hMom z n).1
  obtain ⟨hSumNorm, hSumMean⟩ :=
    avram_a25_factorial_series_norm_summable_mean_20261115
      P K r hr hMom z hz
  have hPointwise (ω : Ω) :
      (∑' n : ℕ, F n ω) = Real.exp (θ * (K ω : ℝ)) := by
    simpa only [F, z] using
      (avram_a25_nat_factorial_exp_tsum_20261115 (K ω) θ)
  have hMean :
      (∫ ω, Real.exp (θ * (K ω : ℝ)) ∂P) =
        Real.exp ((r : ℝ) * z) := by
    calc
      _ = (∫ ω, ∑' n : ℕ, F n ω ∂P) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact (hPointwise ω).symm
      _ = (∑' n : ℕ, ∫ ω, F n ω ∂P) :=
        (integral_tsum_of_summable_integral_norm hFInt hSumNorm).symm
      _ = Real.exp ((r : ℝ) * z) := hSumMean
  have hInt : Integrable (fun ω => Real.exp (θ * (K ω : ℝ))) P :=
    Integrable.of_integral_ne_zero (by
      rw [hMean]
      exact ne_of_gt (Real.exp_pos _))
  exact ⟨hInt, by simpa only [z] using hMean⟩
