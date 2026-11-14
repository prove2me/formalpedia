-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a178_finite_aestrongly_measurable_weighted_Gaussian_cross_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:14:39.513454+00:00
-- url     : https://prove2.me/submissions/5d8dac6c-47fc-413a-827b-531a71dffc1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- An almost-everywhere compact Hessian bound transfers original stopped
Gaussian unweighted quadratic cross integrability to its finite weighted sum. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ℕ) (H R : ℕ → ℕ → Ω → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hHm : ∀ m i, AEStronglyMeasurable (H m i) P)
    (hRm : ∀ m i, AEStronglyMeasurable (R m i) P)
    (hH : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ S m, |H m i ω| ≤ K)
    (hRI : ∀ m, Integrable (fun ω =>
      ∑ i ∈ S m, |R m i ω|) P) :
    ∀ m, Integrable (fun ω =>
      |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P := by
  intro m
  have hSm0 : AEStronglyMeasurable
      (∑ i ∈ S m, fun ω : Ω => H m i ω / 2 * R m i ω) P := by
    exact Finset.aestronglyMeasurable_sum (S m) (fun i hi => by
      have hdiv : AEStronglyMeasurable
          (fun ω => H m i ω / 2) P := by
        simpa only [div_eq_mul_inv] using (hHm m i).mul_const (2 : ℝ)⁻¹
      exact hdiv.mul (hRm m i))
  have hSm : AEStronglyMeasurable
      (fun ω => ∑ i ∈ S m, H m i ω / 2 * R m i ω) P := by
    have hs : (∑ i ∈ S m,
        fun ω : Ω => H m i ω / 2 * R m i ω) =
        (fun ω => ∑ i ∈ S m, H m i ω / 2 * R m i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    simpa only [hs] using hSm0
  have hFm : AEStronglyMeasurable
      (fun ω => |∑ i ∈ S m, H m i ω / 2 * R m i ω|) P := by
    simpa only [Real.norm_eq_abs] using hSm.norm
  have hPoint : ∀ᵐ ω ∂P,
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
        rw [abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (hω i hi) (by norm_num))
          (abs_nonneg _)
      _ = (K / 2) * ∑ i ∈ S m, |R m i ω| := by
        rw [Finset.mul_sum]
  apply ((hRI m).const_mul (K / 2)).mono' hFm
  filter_upwards [hPoint] with ω hω
  have hnonneg : 0 ≤ (K / 2) * (∑ i ∈ S m, |R m i ω|) := by
    apply mul_nonneg (div_nonneg hK (by norm_num))
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  simpa only [Real.norm_eq_abs,abs_abs,abs_of_nonneg hnonneg] using hω
