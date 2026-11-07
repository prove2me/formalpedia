-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:22:23.531232+00:00
-- url     : https://prove2.me/submissions/144aa0ed-71e7-411e-b876-4c2286edab32

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Source-exact two-error bound for a potentially nonintegrable signed
    generator term B, preserving the least positive payoff deficit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F M B ErrCell ErrContact : Ω → ℝ) (base : ℝ)
    (hCell : Integrable (fun ω => max (ErrCell ω) 0) P)
    (hContact : Integrable (fun ω => max (ErrContact ω) 0) P)
    (hExcessMeas : AEStronglyMeasurable
      (fun ω => max (F ω - (base + (M ω + B ω))) 0) P)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ base + (M ω + B ω) +
        max (ErrCell ω) 0 + max (ErrContact ω) 0) :
    Integrable (fun ω => max (F ω - (base + (M ω + B ω))) 0) P ∧
    (∫ ω, max (F ω - (base + (M ω + B ω))) 0 ∂P) ≤
      (∫ ω, max (ErrCell ω) 0 ∂P) +
      (∫ ω, max (ErrContact ω) 0 ∂P) := by
  classical
  let E : Ω → ℝ := fun ω =>
    max (F ω - (base + (M ω + B ω))) 0
  let H : Ω → ℝ := fun ω =>
    max (ErrCell ω) 0 + max (ErrContact ω) 0
  have hH : Integrable H P := hCell.add hContact
  have hE_nonneg (ω : Ω) : 0 ≤ E ω := le_max_right _ _
  have hH_nonneg (ω : Ω) : 0 ≤ H ω := by
    exact add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hBound : ∀ᵐ ω ∂P, E ω ≤ H ω := by
    filter_upwards [hBudget] with ω hω
    change max (F ω - (base + (M ω + B ω))) 0 ≤
      max (ErrCell ω) 0 + max (ErrContact ω) 0
    apply max_le
    · linarith
    · exact hH_nonneg ω
  have hNorm : ∀ᵐ ω ∂P, ‖E ω‖ ≤ H ω := by
    filter_upwards [hBound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hE_nonneg ω)] using hω
  have hE : Integrable E P :=
    hH.mono' (by simpa only [E] using hExcessMeas) hNorm
  refine ⟨by simpa only [E] using hE, ?_⟩
  have hI : (∫ ω, E ω ∂P) ≤ ∫ ω, H ω ∂P :=
    integral_mono_ae hE hH hBound
  simpa only [E, H, integral_add hCell hContact] using hI
