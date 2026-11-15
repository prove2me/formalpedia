-- Prove2me | solution 1 for AvramDividend.Classical.avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:47:08.440466+00:00
-- url     : https://prove2.me/submissions/814ba75c-5778-424d-8b69-663ca008776e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (marked : ℕ → Ω → Finset ℕ)
    (N : Ω → ℝ) (hNI : Integrable N P)
    (hNdom : ∀ m, ∀ᵐ ω ∂P,
      ((marked m ω).card : ℝ) ≤ N ω)
    (W : ℕ → Ω → ℕ → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P)
    (ε : ℕ → ℝ)
    (hεnonneg : ∀ m, 0 ≤ ε m)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hW : ∀ m, ∀ᵐ ω ∂P,
      ∀ i ∈ marked m ω, ‖W m ω i‖ ≤ ε m) :
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ marked m ω, W m ω i
    (∀ m, Integrable (F m) P) ∧
    Tendsto (fun m => ∫ ω, ‖F m ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let F : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ marked m ω, W m ω i
  have hBound (m : ℕ) :
      ∀ᵐ ω ∂P, ‖F m ω‖ ≤ ε m * N ω := by
    filter_upwards [hNdom m, hW m] with ω hdom hw
    calc
      ‖F m ω‖ ≤ ∑ i ∈ marked m ω, ‖W m ω i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ marked m ω, ε m := by
        apply Finset.sum_le_sum
        intro i hi
        exact hw i hi
      _ = ε m * ((marked m ω).card : ℝ) := by
        simp [mul_comm]
      _ ≤ ε m * N ω :=
        mul_le_mul_of_nonneg_left hdom (hεnonneg m)
  have hInt (m : ℕ) : Integrable (F m) P :=
    (hNI.const_mul (ε m)).mono' (hMeas m) (hBound m)
  have hUpper (m : ℕ) :
      (∫ ω, ‖F m ω‖ ∂P) ≤
        ε m * (∫ ω, N ω ∂P) := by
    calc
      (∫ ω, ‖F m ω‖ ∂P) ≤
          ∫ ω, ε m * N ω ∂P := by
        apply integral_mono_ae (hInt m).norm
          (hNI.const_mul (ε m))
        exact hBound m
      _ = ε m * (∫ ω, N ω ∂P) := by
        rw [integral_const_mul]
  constructor
  · exact hInt
  · apply squeeze_zero
      (fun m => integral_nonneg (fun ω => norm_nonneg (F m ω)))
      hUpper
    simpa using hεzero.mul_const (∫ ω, N ω ∂P)
