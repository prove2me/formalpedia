-- Prove2me | solution 1 for AvramDividend.Classical.avram_b47_original_any_bounded_clock_mixed_ledger_L1_condexp_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:20:33.788256+00:00
-- url     : https://prove2.me/submissions/0880967b-12d5-44a9-baf4-a1e2a464565a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True bounded stopped mixed Levy HJB budget from same-source finite-grid ledgers and L1 limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (F : Ω → ℝ) (hFI : Integrable F P) (b : ℝ) :
    ∃ (ρ : ℕ → Ω → ℝ≥0) (S : ℕ → Finset ℝ≥0),
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, ρ k ω ∈ S k) ∧
      (∀ k ω, τ ω ≤ ρ k ω ∧ ρ k ω ≤ (n : ℝ≥0)) ∧
      (∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) ∧
      ∀ (Fseq Bseq : ℕ → Ω → ℝ),
        (∀ k, Integrable (Fseq k) P) →
        (∀ k, ∀ᵐ ω ∂P, Bseq k ω ≤ 0) →
        (∀ k (R Jsmall : ℝ≥0 → Ω → ℝ),
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
            (fun j : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
            atTop (𝓝 (R t ω))) →
          (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
            (fun j : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X j t ω)
            atTop (𝓝 (Jsmall t ω))) →
          ∀ᵐ ω ∂P,
            Fseq k ω ≤ b + R (ρ k ω) ω + Jsmall (ρ k ω) ω + Bseq k ω) →
        (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
          Tendsto (fun k => ∫⁻ ω in A,
            ‖Fseq k ω - F ω‖ₑ ∂P)
            atTop (𝓝 (0 : ℝ≥0∞))) →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨ρ, hStop, hRanges, hGe, hLe, hLim⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops
      τ hτstop n hτbound
  choose S hRange using hRanges
  refine ⟨ρ, S, hStop, hRange, ?_, hLim, ?_⟩
  · exact fun k ω => ⟨hGe k ω, hLe k ω⟩
  intro Fseq Bseq hFkI hBsign hLedger hL1
  apply avram_ubv_finite14_initial_event_budget_to_condexp
    F b hFI
  intro A hA
  have hBound (k : ℕ) :
      (∫ ω in A, Fseq k ω ∂P) ≤ b * (P A).toReal :=
    avram_b42_original_finite_range_physical_ledger_budget
      X hX hFinite n hn (ρ k) (hStop k) (hLe k)
      (S k) (hRange k) A hA b (Fseq k) (Bseq k)
      (hFkI k) (ae_restrict_of_ae (hBsign k))
      (fun R J hR hJ =>
        ae_restrict_of_ae (hLedger k R J hR hJ))
  have hIntegralLimit :=
    tendsto_integral_of_L1 F hFI.integrableOn.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k => (hFkI k).integrableOn))
      (hL1 A hA)
  exact le_of_tendsto hIntegralLimit
    (Filter.Eventually.of_forall hBound)
