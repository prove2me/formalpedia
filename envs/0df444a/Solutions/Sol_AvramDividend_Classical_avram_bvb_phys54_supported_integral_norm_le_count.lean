-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys54_supported_integral_norm_le_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:46:23.53483+00:00
-- url     : https://prove2.me/submissions/9b2d7407-7211-42cd-a043-5faeecc1b747

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Finite measure of the support converts a uniform reward envelope into an integral bound. -/
theorem solution
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Set α) (hSm : MeasurableSet S) (hFinite : μ S < ⊤)
    (f : α → ℝ) (hf : Integrable f μ)
    (hSupport : ∀ a, a ∉ S → f a = 0)
    (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ a ∈ S, ‖f a‖ ≤ K) :
    ‖∫ a, f a ∂μ‖ ≤ K * (μ S).toReal := by
  have hEq : f =ᵐ[μ] S.indicator f := by
    filter_upwards [] with a
    by_cases ha : a ∈ S
    · simp [Set.indicator_of_mem ha]
    · simp [Set.indicator_of_notMem ha, hSupport a ha]
  have hIntegral : (∫ a, f a ∂μ) = ∫ a in S, f a ∂μ := by
    calc
      (∫ a, f a ∂μ) = ∫ a, S.indicator f a ∂μ :=
        integral_congr_ae hEq
      _ = ∫ a in S, f a ∂μ := integral_indicator hSm
  letI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hFinite⟩
  have hBoundAE : ∀ᵐ a ∂μ.restrict S, ‖f a‖ ≤ K :=
    ae_restrict_of_forall_mem hSm hBound
  rw [hIntegral]
  simpa [Measure.real, Measure.restrict_apply_univ] using
    (norm_integral_le_of_norm_le_const hBoundAE)
