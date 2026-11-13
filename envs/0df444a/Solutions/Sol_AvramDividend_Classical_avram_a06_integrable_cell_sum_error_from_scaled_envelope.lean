-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_integrable_cell_sum_error_from_scaled_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:39:03.594105+00:00
-- url     : https://prove2.me/submissions/bef5bf17-6d5f-4d9e-a260-c00504acb67d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E U : ℕ → Ω → ℝ)
    (hEI : ∀ n, Integrable (E n) P)
    (hENonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω)
    (hScaled : Tendsto
      (fun (n : ℕ) => ((n : ℝ) + 1) * (∫ ω, E n ω ∂P))
      atTop (𝓝 (0 : ℝ)))
    (hUMeas : ∀ n, AEStronglyMeasurable (U n) P)
    (hUBound : ∀ n, ∀ᵐ ω ∂P,
      0 ≤ U n ω ∧ U n ω ≤ ((n : ℝ) + 1) * E n ω) :
    (∀ n, Integrable (U n) P) ∧
    Tendsto (fun n => ∫ ω, U n ω ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  have hScaledI (n : ℕ) : Integrable
      (fun ω => ((n : ℝ) + 1) * E n ω) P :=
    (hEI n).const_mul _
  have hUI (n : ℕ) : Integrable (U n) P := by
    apply (hScaledI n).mono' (hUMeas n)
    filter_upwards [hENonneg n, hUBound n] with ω hE hU
    have hMult : 0 ≤ ((n : ℝ) + 1) * E n ω :=
      mul_nonneg (by positivity) hE
    simpa only [Real.norm_eq_abs, abs_of_nonneg hU.1,
      abs_of_nonneg hMult] using hU.2
  refine ⟨hUI, ?_⟩
  have hLower (n : ℕ) : 0 ≤ ∫ ω, U n ω ∂P :=
    integral_nonneg_of_ae ((hUBound n).mono (fun ω h => h.1))
  have hUpper (n : ℕ) :
      (∫ ω, U n ω ∂P) ≤
        ((n : ℝ) + 1) * (∫ ω, E n ω ∂P) := by
    have hM := integral_mono_ae (hUI n) (hScaledI n)
      ((hUBound n).mono (fun ω h => h.2))
    simpa only [integral_const_mul] using hM
  exact squeeze_zero hLower hUpper hScaled
