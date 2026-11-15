-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_marked_physical_weighted_contact_L1_vanish_from_count_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:36:03.703502+00:00
-- url     : https://prove2.me/submissions/440fba4c-b706-464c-a77f-12624ed6c5bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (marked : ℕ → Ω → Finset ℕ) (W : ℕ → ℕ → Ω → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hCount : ∀ k, ∀ᵐ ω ∂P, ((marked k ω).card : ℝ) ≤ B ω)
    (hWeight : ∀ k i ω, |W k i ω| ≤ L)
    (hMeas : ∀ k, AEStronglyMeasurable
      (fun ω => |∑ i ∈ marked k ω, W k i ω|) P)
    (hPoint : ∀ᵐ ω ∂P, Tendsto
      (fun k => ∑ i ∈ marked k ω, W k i ω)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, |∑ i ∈ marked k ω, W k i ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hDom (k : ℕ) :
      ∀ᵐ ω ∂P, ‖|∑ i ∈ marked k ω, W k i ω|‖ ≤ L * B ω := by
    filter_upwards [hCount k] with ω hc
    calc
      ‖|∑ i ∈ marked k ω, W k i ω|‖
        = |∑ i ∈ marked k ω, W k i ω| := by simp
      _ ≤ ∑ i ∈ marked k ω, |W k i ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ marked k ω, L := by
        apply Finset.sum_le_sum
        intro i hi
        exact hWeight k i ω
      _ = L * ((marked k ω).card : ℝ) := by
        simp [mul_comm]
      _ ≤ L * B ω := mul_le_mul_of_nonneg_left hc hL
  have hAbs : ∀ᵐ ω ∂P,
      Tendsto (fun k => |∑ i ∈ marked k ω, W k i ω|)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hPoint] with ω hw
    simpa only [abs_zero] using hw.abs
  have hDCT :=
    tendsto_integral_of_dominated_convergence
      (fun ω => L * B ω) hMeas (hBI.const_mul L) hDom hAbs
  simpa only [integral_zero] using hDCT
