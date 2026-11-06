-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_pair_sum_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:39:59.997206+00:00
-- url     : https://prove2.me/submissions/ce7ad8db-6f79-4021-9914-5575f07025bb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band ordered jump-pair corrections have an L1
    bound of second physical order for bounded kernels. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (Pairs : Ω → Finset (ℝ≥0 × ℝ≥0))
    (hPairs : ∀ ω p, p ∈ Pairs ω →
      p.1 ∈ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ∧
      p.2 ∈ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))} ∧ p.1 ≠ p.2)
    (hPairCard : ∀ ω, ((Pairs ω).card : ℝ) =
      ({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) *
      (({u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard : ℝ) - 1))
    (H : (ℝ≥0 × ℝ≥0) → Ω → ℝ)
    (hSumMeas : Measurable (fun ω =>
      (Pairs ω).sum (fun p => H p ω)))
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ p ω, |H p ω| ≤ B) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (Pairs ω).sum (fun p => H p ω)) P ∧
    (∫ ω, |(Pairs ω).sum (fun p => H p ω)| ∂P) ≤ B * r ^ 2 := by
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (Pairs ω).sum (fun p => H p ω)) P ∧
    (∫ ω, |(Pairs ω).sum (fun p => H p ω)| ∂P) ≤ B * r ^ 2
  have hFactor :=
    avram_p4_s3_original_bounded_stop_negative_band_factorial_pair_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) P ∧
    (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) ≤ r ^ 2 at hFactor
  have hBound (ω : Ω) :
      |(Pairs ω).sum (fun p => H p ω)| ≤
      B * ((K ω : ℝ) * ((K ω : ℝ) - 1)) := by
    calc
      |(Pairs ω).sum (fun p => H p ω)|
          ≤ (Pairs ω).sum (fun p => |H p ω|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ (Pairs ω).sum (fun _ => B) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hH p ω
      _ = B * ((K ω : ℝ) * ((K ω : ℝ) - 1)) := by
        calc
          (Pairs ω).sum (fun _ => B) =
              ((Pairs ω).card : ℝ) * B := by
                simp only [Finset.sum_const, nsmul_eq_mul]
          _ = B * ((K ω : ℝ) * ((K ω : ℝ) - 1)) := by
            rw [hPairCard ω]
            ring
  have hNonneg (k : ℕ) : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    cases k with
    | zero => norm_num
    | succ j =>
      have hj : (1 : ℝ) ≤ (Nat.succ j : ℝ) := by
        exact_mod_cast (show 1 ≤ Nat.succ j by omega)
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hj)
  have hMajor : Integrable
      (fun ω => B * ((K ω : ℝ) * ((K ω : ℝ) - 1))) P :=
    hFactor.1.const_mul B
  have hSumI : Integrable (fun ω => (Pairs ω).sum (fun p => H p ω)) P := by
    apply Integrable.mono hMajor hSumMeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(Pairs ω).sum (fun p => H p ω)‖ ≤
      ‖B * ((K ω : ℝ) * ((K ω : ℝ) - 1))‖
    rw [Real.norm_eq_abs,
      Real.norm_of_nonneg (mul_nonneg hB (hNonneg (K ω)))]
    exact hBound ω
  refine ⟨hSumI, ?_⟩
  have hIntegral := integral_mono_ae hSumI.abs hMajor
    (Filter.Eventually.of_forall hBound)
  calc
    (∫ ω, |(Pairs ω).sum (fun p => H p ω)| ∂P)
        ≤ ∫ ω, B * ((K ω : ℝ) * ((K ω : ℝ) - 1)) ∂P := hIntegral
    _ = B * (∫ ω, (K ω : ℝ) * ((K ω : ℝ) - 1) ∂P) := by
      rw [integral_const_mul]
    _ ≤ B * r ^ 2 := mul_le_mul_of_nonneg_left hFactor.2 hB
