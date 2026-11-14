-- Prove2me | solution 2 for AvramDividend.Classical.avram_b46_original_finite_range_signed_ledger_condexp_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:21:02.776284+00:00
-- url     : https://prove2.me/submissions/b0e317d7-02bd-4a57-bcff-3b20ede11892

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-range mixed signed physical ledger implies time-zero conditional reward bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (b : ℝ) (F B : Ω → ℝ) (hFI : Integrable F P)
    (hBsign : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hLedger : ∀ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂P,
        F ω ≤ b + R (τ ω) ω + Jsmall (τ ω) ω + B ω) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  apply avram_ubv_finite14_initial_event_budget_to_condexp
    F b hFI
  intro A hA
  exact avram_b42_original_finite_range_physical_ledger_budget
    X hX hFinite n hn τ hτstop hτbound S hτrange
    A hA b F B hFI
    (ae_restrict_of_ae hBsign)
    (fun R Jsmall hR hJ =>
      ae_restrict_of_ae (hLedger R Jsmall hR hJ))
