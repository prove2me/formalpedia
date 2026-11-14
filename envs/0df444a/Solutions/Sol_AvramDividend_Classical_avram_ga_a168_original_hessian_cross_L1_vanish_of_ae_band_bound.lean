-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a168_original_hessian_cross_L1_vanish_of_ae_band_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:45:58.275136+00:00
-- url     : https://prove2.me/submissions/b7b8431e-3a07-463c-8456-227ad52db7a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- A uniform almost-everywhere C2 coefficient bound suffices for expected
absolute L1 convergence of physical Gaussian quadratic cross corrections. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ) (H R : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ S m, |H m i ω| ≤ K)
    (hCrossI : ∀ m, Integrable (fun ω =>
      |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P)
    (hEnergyI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, |R m i ω|) P)
    (hEnergyL1 : Tendsto (fun m =>
      ∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m =>
      ∫ ω, |∑ i ∈ S m, H m i ω / 2 * R m i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  have hPoint (m : ℕ) : ∀ᵐ ω ∂P,
      |∑ i ∈ S m, H m i ω / 2 * R m i ω| ≤
        (K / 2) * (∑ i ∈ S m, |R m i ω|) := by
    filter_upwards [hH m] with ω hω
    calc
      |∑ i ∈ S m, H m i ω / 2 * R m i ω| ≤
        ∑ i ∈ S m, |H m i ω / 2 * R m i ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S m, (K / 2) * |R m i ω| := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (hω i hi) (by norm_num))
          (abs_nonneg _)
      _ = (K / 2) * (∑ i ∈ S m, |R m i ω|) := by
        rw [Finset.mul_sum]
  have hUpper (m : ℕ) :
      (∫ ω, |∑ i ∈ S m, H m i ω / 2 * R m i ω| ∂P) ≤
        (K / 2) * (∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P) := by
    calc
      (∫ ω, |∑ i ∈ S m, H m i ω / 2 * R m i ω| ∂P) ≤
        (∫ ω, (K / 2) * (∑ i ∈ S m, |R m i ω|) ∂P) :=
          integral_mono_ae (hCrossI m) ((hEnergyI m).const_mul _) (hPoint m)
      _ = (K / 2) * (∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P) := by
        rw [integral_const_mul]
  have hLimit : Tendsto (fun m =>
      (K / 2) * (∫ ω, (∑ i ∈ S m, |R m i ω|) ∂P))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hEnergyL1.const_mul (K / 2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hLimit
    (Filter.Eventually.of_forall (fun m =>
      integral_nonneg (fun ω => abs_nonneg _)))
    (Filter.Eventually.of_forall hUpper)
