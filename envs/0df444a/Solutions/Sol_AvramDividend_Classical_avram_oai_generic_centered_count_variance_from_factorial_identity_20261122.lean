-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_generic_centered_count_variance_from_factorial_identity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:22:14.729256+00:00
-- url     : https://prove2.me/submissions/e3177c05-ad5f-4426-8108-0ef9c367ec48

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N K : Ω → ℝ) (r : ℝ)
    (hN : Integrable N P)
    (hK : Integrable (fun ω => 2 * K ω) P)
    (hMean : (∫ ω, N ω ∂P) = r)
    (hPairs : (∫ ω, 2 * K ω ∂P) = r ^ 2)
    (hFactorial : ∀ᵐ ω ∂P, N ω * (N ω - 1) = 2 * K ω) :
    Integrable (fun ω => (N ω - r) ^ 2) P ∧
    (∫ ω, (N ω - r) ^ 2 ∂P) = r  := by
  have hR : Integrable
      (fun ω => 2 * K ω + (1 - 2 * r) * N ω + r ^ 2) P :=
    (hK.add (hN.const_mul (1 - 2 * r))).add (integrable_const _)
  have hAE : (fun ω => (N ω - r) ^ 2) =ᵐ[P]
      (fun ω => 2 * K ω + (1 - 2 * r) * N ω + r ^ 2) := by
    filter_upwards [hFactorial] with ω hf
    nlinarith [hf]
  have hL : Integrable (fun ω => (N ω - r) ^ 2) P :=
    hR.congr hAE.symm
  refine ⟨hL, ?_⟩
  calc
    (∫ ω, (N ω - r) ^ 2 ∂P) =
        ∫ ω, 2 * K ω + (1 - 2 * r) * N ω + r ^ 2 ∂P :=
      integral_congr_ae hAE
    _ = (∫ ω, 2 * K ω ∂P) +
        (1 - 2 * r) * (∫ ω, N ω ∂P) + r ^ 2 := by
      have hA := integral_add
        (hK.add (hN.const_mul (1 - 2 * r))) (integrable_const (r ^ 2))
      have hB := integral_add hK (hN.const_mul (1 - 2 * r))
      simp only [Pi.add_apply, integral_const_mul, integral_const,
        measure_univ, ENNReal.toReal_one, one_smul, one_mul] at hA hB
      rw [hB] at hA
      simpa [integral_const_mul] using hA
    _ = r := by rw [hPairs, hMean]; ring
