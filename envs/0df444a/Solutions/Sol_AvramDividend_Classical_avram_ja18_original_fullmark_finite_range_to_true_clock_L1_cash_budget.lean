-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_fullmark_finite_range_to_true_clock_L1_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:58:32.0572+00:00
-- url     : https://prove2.me/submissions/5dce069f-56c9-4a05-b00b-131d4e64cccf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Physical fullmark signed cash bounds pass to the true reward by restricted L1 convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (τ : ℕ → Ω → ℝ≥0)
    (hτstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ k ω : WithTop ℝ≥0)))
    (hτbound : ∀ k ω, τ k ω ≤ (n : ℝ≥0))
    (S : ℕ → Finset ℝ≥0) (hτrange : ∀ k ω, τ k ω ∈ S k)
    (F : Ω → ℝ) (Fseq : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, Fseq k ω =
      Real.exp (-(q * (τ k ω : ℝ))) *
        w (if τ k ω = 0 ∨ (τ k ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ k ω) ω - rightLimit D (τ k ω) ω
          else riskProcess X x D (τ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFkI : ∀ k, Integrable (Fseq k) P)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (hb : 0 ≤ b)
    (hIto : ∀ k (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) →
      ∃ B : Ω → ℝ,
        (∀ᵐ ω ∂(P.restrict A), B ω ≤ 0) ∧
        (∀ᵐ ω ∂(P.restrict A),
          Fseq k ω ≤ b + R (τ k ω) ω + Jfull (τ k ω) ω + B ω))
    (hL1 : Tendsto (fun k => ∫⁻ ω in A,
      ‖Fseq k ω - F ω‖ₑ ∂P) atTop (𝓝 (0 : ℝ≥0∞))) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by
  have hBudget (k : ℕ) :
      (∫ ω in A, Fseq k ω ∂P) ≤ b * (P A).toReal :=
    avram_ja18_original_finite_range_fullmark_signed_ito_initial_event_budget
      X hX hFinite q x w D n hn (τ k) (hτstop k) (hτbound k)
      (S k) (hτrange k) (Fseq k) (hFsource k)
      (hFkI k) A A hA (Subset.rfl) b hb (hIto k)
  have hT :=
    tendsto_integral_of_L1 F hFI.integrableOn.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun k => (hFkI k).integrableOn))
      hL1
  exact le_of_tendsto hT (Filter.Eventually.of_forall hBudget)
