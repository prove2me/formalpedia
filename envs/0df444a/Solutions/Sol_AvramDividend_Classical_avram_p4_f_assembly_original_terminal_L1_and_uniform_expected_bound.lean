-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:00:31.317362+00:00
-- url     : https://prove2.me/submissions/eb3c5701-9727-406c-b063-d40cc7711024

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
import Theorems.Thm_avram_p4_f_assembly_original_terminal_mean_bound_integrability_01a5e3a1
import Theorems.Thm_avram_p4_f_assembly_original_terminal_mean_bound_identity_532fd08c
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped terminal L1 and quantitative source Esscher expectation bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    Integrable Term P ∧
      (∫ ω, Term ω ∂P) ≤
        (K * Real.exp (θ * x)) *
          Real.exp (|X.ψ θ - q| * (H : ℝ)) := by
  have hSrc : Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := avram_p4_f_assembly_original_terminal_mean_bound_integrability_01a5e3a1 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (C := C) (x := x) (D := D) (hD := hD) (τ := τ) (W := W) (Term := Term) (hτmeas := hτmeas) (hstop := hstop) (H := H) (hbound := hbound) (hW := hW) (w := w) (q := q) (θ := θ) (K := K) (hθ := hθ) (hK := hK) (hwGrowth := hwGrowth) (hTerm := hTerm) (hTermMeas := hTermMeas) (hTermNonneg := hTermNonneg)
  have hRawEq : (fun ω => Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) =
      (fun ω => (K * Real.exp (θ * x)) *
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) := avram_p4_f_assembly_original_terminal_mean_bound_identity_532fd08c (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (C := C) (x := x) (D := D) (hD := hD) (τ := τ) (W := W) (Term := Term) (hτmeas := hτmeas) (hstop := hstop) (H := H) (hbound := hbound) (hW := hW) (w := w) (q := q) (θ := θ) (K := K) (hθ := hθ) (hK := hK) (hwGrowth := hwGrowth) (hTerm := hTerm) (hTermMeas := hTermMeas) (hTermNonneg := hTermNonneg) (hSrc := hSrc)
  have hRawI : Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) P := by
    rw [hRawEq]
    exact hSrc.const_mul _
  have hUpper :=
    avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
      X C x D hD τ W Term hW w q θ K hθ hK hwGrowth hTerm
  have hTermI : Integrable Term P :=
    hRawI.mono_nonneg hTermMeas hTermNonneg
      (Filter.Eventually.of_forall hUpper)
  refine ⟨hTermI, ?_⟩
  have hMoment :=
    avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
      X θ hθ q τ hstop H hbound
  have hConst : 0 ≤ K * Real.exp (θ * x) :=
    mul_nonneg hK (le_of_lt (Real.exp_pos _))
  calc
    (∫ ω, Term ω ∂P) ≤
        ∫ ω, Real.exp (-(q * (τ ω : ℝ))) *
          (K * Real.exp (θ * (x + X.X (τ ω) ω))) ∂P :=
      integral_mono_of_nonneg hTermNonneg hRawI
        (Filter.Eventually.of_forall hUpper)
    _ = ∫ ω, (K * Real.exp (θ * x)) *
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P := by
      rw [hRawEq]
    _ = (K * Real.exp (θ * x)) *
        (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) := by
      rw [integral_const_mul]
    _ ≤ (K * Real.exp (θ * x)) *
        Real.exp (|X.ψ θ - q| * (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hMoment hConst
