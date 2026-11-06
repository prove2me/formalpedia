-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_stopped_actual_jump_sum_shorttime_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:23.640582+00:00
-- url     : https://prove2.me/submissions/5fd95c8f-e983-4e0e-b038-5c125054b51e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτBound : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0))
    (hKmeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard))
    (f : ℕ → Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ k ω u, |f k ω u| ≤ B)
    (hErrMeas : ∀ k : ℕ, AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (τ k ω) n).toFinset, f k ω u
      else 0) P) :
    let F : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (τ k ω) n).toFinset
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, ‖if 2 ≤ K k ω then ∑ u ∈ F k ω, f k ω u else 0‖ ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by
  classical
  let F : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
    (avram_wave7_06_original_negative_band_marked_times_finite
      X ω (τ k ω) n).toFinset
  let K : ℕ → Ω → ℕ := fun k ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let ν : ℝ≥0∞ := X.ν (Iic (-(1 / ((n : ℝ) + 1))))
  let I : ℕ → ℝ := fun k =>
    ∫ ω, ‖if 2 ≤ K k ω then ∑ u ∈ F k ω, f k ω u else 0‖ ∂P
  change Tendsto I atTop (nhds (0 : ℝ))
  have hBound (k : ℕ) :
      I k ≤ B * ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * ν).toReal) ^ 2 := by
    have h := avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
      X (T / (k : ℝ≥0)) n (τ k) (hτBound k) (hKmeas k)
      (f k) B hB (hf k) (hErrMeas k)
    exact h.2
  have hNonneg (k : ℕ) : 0 ≤ I k := by
    change 0 ≤ ∫ ω, ‖if 2 ≤ K k ω then
      ∑ u ∈ F k ω, f k ω u else 0‖ ∂P
    apply integral_nonneg
    intro ω
    exact norm_nonneg _
  have hInv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let a : ℝ := (T : ℝ) * ν.toReal
  have hRate : Tendsto (fun k : ℕ => a / (k : ℝ))
      atTop (nhds (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => a) atTop (nhds a) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hConst.mul hInv
  have hUpperLimit : Tendsto (fun k : ℕ => B * (a / (k : ℝ)) ^ 2)
      atTop (nhds (0 : ℝ)) := by
    have hBconst : Tendsto (fun _ : ℕ => B) atTop (nhds B) :=
      tendsto_const_nhds
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero] using
      hBconst.mul (hRate.pow 2)
  have hUpper : ∀ᶠ k : ℕ in atTop, I k ≤ B * (a / (k : ℝ)) ^ 2 :=
    (eventually_gt_atTop (0 : ℕ)).mono (fun k hk => by
      have hr := avram_p4_f2_physical_horizon_rate_real_div T ν k hk
      have hkNN : (k : ℝ≥0) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hk)
      have hb := hBound k
      rw [ENNReal.coe_div hkNN, hr] at hb
      exact hb)
  have hLower : ∀ᶠ k : ℕ in atTop, (0 : ℝ) ≤ I k :=
    Filter.Eventually.of_forall hNonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (nhds (0 : ℝ))) hUpperLimit hLower hUpper
