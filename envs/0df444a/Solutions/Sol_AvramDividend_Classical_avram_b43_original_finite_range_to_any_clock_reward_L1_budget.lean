-- Prove2me | solution 1 for AvramDividend.Classical.avram_b43_original_finite_range_to_any_clock_reward_L1_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:33.857409+00:00
-- url     : https://prove2.me/submissions/e56ab076-967f-4a6f-a930-44a6bb59ec96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-range signed mixed stopped Ito budget passes to a true L1 stopped reward limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F : Ω → ℝ) (Fseq Bseq : ℕ → Ω → ℝ)
    (hFI : Integrable F P) (hFkI : ∀ k, Integrable (Fseq k) P)
    (hBsign : ∀ k, ∀ᵐ ω ∂(P.restrict A), Bseq k ω ≤ 0)
    (hLedger : ∀ k (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun j : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun j : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂(P.restrict A),
        Fseq k ω ≤ b + R (τ k ω) ω + Jsmall (τ k ω) ω + Bseq k ω)
    (hL1 : Tendsto (fun k => ∫⁻ ω in A,
      ‖Fseq k ω - F ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞))) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by 
  classical
  have hBound (k : ℕ) :
      (∫ ω in A, Fseq k ω ∂P) ≤ b * (P A).toReal :=
    avram_b42_original_finite_range_physical_ledger_budget
      X hX hFinite n hn (τ k) (hτstop k) (hτbound k)
      (S k) (hτrange k) A hA b (Fseq k) (Bseq k)
      (hFkI k) (hBsign k) (hLedger k)
  have hT :=
    tendsto_integral_of_L1 F hFI.integrableOn.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k => (hFkI k).integrableOn))
      hL1
  exact le_of_tendsto hT (Filter.Eventually.of_forall hBound)
