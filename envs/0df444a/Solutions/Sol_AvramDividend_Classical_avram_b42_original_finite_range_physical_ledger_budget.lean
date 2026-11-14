-- Prove2me | solution 1 for AvramDividend.Classical.avram_b42_original_finite_range_physical_ledger_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:05:51.422198+00:00
-- url     : https://prove2.me/submissions/980cf85d-9079-4329-a697-28a515554886

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b40_original_finite_range_intrinsic_centered_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-range original mixed stopped source HJB ledger implies eventwise budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F B : Ω → ℝ) (hFI : Integrable F P)
    (hBsign : ∀ᵐ ω ∂(P.restrict A), B ω ≤ 0)
    (hLedger : ∀ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂(P.restrict A),
        F ω ≤ b + R (τ ω) ω + Jsmall (τ ω) ω + B ω) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨R, Jsmall, M, hRsrc, hJsrc, hMI, hMzero, hMsrc, hMmean⟩ :=
    avram_b40_original_finite_range_intrinsic_centered_sum
      X hX hFinite n hn τ hτstop hτbound S hτrange A hA
  have hUpper : ∀ᵐ ω ∂(P.restrict A), F ω ≤ b + M ω := by
    filter_upwards [hLedger R Jsmall hRsrc hJsrc, hBsign]
      with ω hF hB
    rw [hMsrc ω]
    linarith
  have hMeanBound :=
    integral_mono_ae hFI.integrableOn
      ((integrable_const b).add hMI).integrableOn hUpper
  calc
    (∫ ω in A, F ω ∂P) ≤
        ∫ ω in A, b + M ω ∂P := hMeanBound
    _ = b * (P A).toReal := by
      calc
        (∫ ω in A, b + M ω ∂P) =
            (∫ ω in A, (b : ℝ) ∂P) +
              (∫ ω in A, M ω ∂P) :=
          integral_add (integrable_const b).integrableOn hMI.integrableOn
        _ = (P A).toReal * b + 0 := by
          rw [hMmean]
          simp only [setIntegral_const, smul_eq_mul, Measure.real]
        _ = b * (P A).toReal := by ring
