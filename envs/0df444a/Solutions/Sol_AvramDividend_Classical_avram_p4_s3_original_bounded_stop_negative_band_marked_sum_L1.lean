-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_marked_sum_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:24:14.726015+00:00
-- url     : https://prove2.me/submissions/e8ca69dd-3d6b-4c4b-9d1b-6682c6c859c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original finite-band marked jump sum with bounded coefficients
    has an L1 envelope controlled by the true physical compensator rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω, (↑(F ω) : Set ℝ≥0) = {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))})
    (hKmeas : Measurable (fun ω : Ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard))
    (H : ℝ≥0 → Ω → ℝ)
    (hSumMeas : Measurable (fun ω => (F ω).sum (fun u => H u ω)))
    (B : ℝ) (hB : 0 ≤ B) (hH : ∀ u ω, |H u ω| ≤ B) :
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (F ω).sum (fun u => H u ω)) P ∧
    (∫ ω, |(F ω).sum (fun u => H u ω)| ∂P) ≤ B * r := by
  classical
  let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change Integrable (fun ω => (F ω).sum (fun u => H u ω)) P ∧
    (∫ ω, |(F ω).sum (fun u => H u ω)| ∂P) ≤ B * r
  have hFirst :=
    avram_p4_s3_original_bounded_stop_negative_band_count_L1_first_moment
      X T n τ hτ hKmeas
  change Integrable (fun ω => (K ω : ℝ)) P ∧
    (∫ ω, (K ω : ℝ) ∂P) ≤ r at hFirst
  have hCard (ω : Ω) : (F ω).card = K ω := by
    calc
      (F ω).card = (↑(F ω) : Set ℝ≥0).ncard :=
        (Set.ncard_coe_finset (F ω)).symm
      _ = K ω := by rw [hF ω]
  have hPointwise (ω : Ω) :
      |(F ω).sum (fun u => H u ω)| ≤ B * (K ω : ℝ) := by
    calc
      |(F ω).sum (fun u => H u ω)|
          ≤ (F ω).sum (fun u => |H u ω|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ (F ω).sum (fun _ => B) := by
        apply Finset.sum_le_sum
        intro u hu
        exact hH u ω
      _ = B * (K ω : ℝ) := by simp [hCard ω, mul_comm]
  have hMajor : Integrable (fun ω => B * (K ω : ℝ)) P :=
    hFirst.1.const_mul B
  have hSumI : Integrable (fun ω => (F ω).sum (fun u => H u ω)) P := by
    apply Integrable.mono hMajor hSumMeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(F ω).sum (fun u => H u ω)‖ ≤ ‖B * (K ω : ℝ)‖
    rw [Real.norm_eq_abs,
      Real.norm_of_nonneg (mul_nonneg hB (Nat.cast_nonneg _))]
    exact hPointwise ω
  refine ⟨hSumI, ?_⟩
  have hIntegral := integral_mono_ae hSumI.abs hMajor
    (Filter.Eventually.of_forall hPointwise)
  calc
    (∫ ω, |(F ω).sum (fun u => H u ω)| ∂P)
        ≤ ∫ ω, B * (K ω : ℝ) ∂P := hIntegral
    _ = B * (∫ ω, (K ω : ℝ) ∂P) := by rw [integral_const_mul]
    _ ≤ B * r := mul_le_mul_of_nonneg_left hFirst.2 hB
