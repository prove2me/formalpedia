-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:26:25.732727+00:00
-- url     : https://prove2.me/submissions/74f78f89-3d97-4c38-a47f-cca7515776bb

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- Dominated closure of signed physical mark compensators with random clocks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (J N ρ : Ω → ℝ)
    (c : ℕ → ℝ) (r M T : ℝ)
    (hT : 0 ≤ T)
    (hFI : ∀ k, Integrable (F k) P)
    (hNI : Integrable N P) (hρI : Integrable ρ P)
    (hρ : ∀ ω, 0 ≤ ρ ω ∧ ρ ω ≤ T)
    (hFBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ N ω)
    (hcBound : ∀ k, |c k| ≤ M)
    (hFConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (J ω)))
    (hcConv : Tendsto c atTop (𝓝 r)) :
    Tendsto (fun k => ∫ ω, F k ω - ρ ω * c k ∂P)
      atTop (𝓝 (∫ ω, J ω - ρ ω * r ∂P)) := by
  have hM : 0 ≤ M :=
    (abs_nonneg (c 0)).trans (hcBound 0)
  have hEnv : Integrable (fun ω => N ω + T * M) P :=
    hNI.add (integrable_const _)
  have hMeas : ∀ k, AEStronglyMeasurable
      (fun ω => F k ω - ρ ω * c k) P := by
    intro k
    exact (hFI k).aestronglyMeasurable.sub
      (hρI.aestronglyMeasurable.mul aestronglyMeasurable_const)
  have hDom : ∀ k, ∀ᵐ ω ∂P,
      ‖F k ω - ρ ω * c k‖ ≤ N ω + T * M := by
    intro k
    filter_upwards [hFBound] with ω hω
    have hc : ‖c k‖ ≤ M := by
      simpa only [Real.norm_eq_abs] using hcBound k
    have hρc : ‖ρ ω * c k‖ ≤ T * M := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ ω).1]
      exact (mul_le_mul_of_nonneg_right (hρ ω).2 (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hc hT)
    exact (norm_sub_le (F k ω) (ρ ω * c k)).trans
      (add_le_add (hω k) hρc)
  have hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω - ρ ω * c k)
        atTop (𝓝 (J ω - ρ ω * r)) := by
    filter_upwards [hFConv] with ω hω
    exact hω.sub (tendsto_const_nhds.mul hcConv)
  exact tendsto_integral_of_dominated_convergence
    (fun ω => N ω + T * M) hMeas hEnv hDom hLimit
