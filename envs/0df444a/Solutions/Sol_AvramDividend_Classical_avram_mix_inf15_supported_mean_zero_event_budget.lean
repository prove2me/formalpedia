-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf15_supported_mean_zero_event_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T12:58:15.555488+00:00
-- url     : https://prove2.me/submissions/7eec4a07-7c5c-4a93-a9ad-8446618ddb84

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (b : ℝ) (F M : Ω → ℝ)
    (hFI : Integrable F P) (hMI : Integrable M P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hMoff : ∀ᵐ ω ∂P, ω ∉ A → M ω = 0)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ b + M ω) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by
  have hSupported : (A.indicator M) =ᵐ[P] M := by
    filter_upwards [hMoff] with ω hω
    by_cases ha : ω ∈ A
    · simp [Set.indicator_of_mem ha]
    · simp [Set.indicator_of_notMem ha, hω ha]
  have hSetZero : (∫ ω in A, M ω ∂P) = 0 := by
    calc
      (∫ ω in A, M ω ∂P) = ∫ ω, A.indicator M ω ∂P :=
        (integral_indicator hA).symm
      _ = ∫ ω, M ω ∂P := integral_congr_ae hSupported
      _ = 0 := hMzero
  have hAddI : Integrable (fun ω => b + M ω) P :=
    (integrable_const b).add hMI
  calc
    (∫ ω in A, F ω ∂P) ≤ ∫ ω in A, b + M ω ∂P :=
      setIntegral_mono_ae hFI.integrableOn hAddI.integrableOn hUpper
    _ = (∫ _ in A, b ∂P) + (∫ ω in A, M ω ∂P) :=
      integral_add (integrable_const b).integrableOn hMI.integrableOn
    _ = b * (P A).toReal := by
      rw [hSetZero, add_zero, setIntegral_const]
      simp [smul_eq_mul, Measure.real, mul_comm]
