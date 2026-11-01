-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:42:02.479167+00:00
-- url     : https://prove2.me/submissions/ce38d5d0-0f9d-44bd-84a8-4baed844fe87

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Under the actual stopped interior gradient condition, the real signed
continuous Stieltjes dividend correction is nonpositive against any atomless
time measure, including one with singular-continuous variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)) ν) :
    (∫ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) ≤ 0 := by
  let E : Set ℝ := paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)
  let g : ℝ → ℝ := fun s =>
    Real.exp (-q * s) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω))
  have hMeas : MeasurableSet E :=
    (paymentTimes_measurable τ).inter measurableSet_Icc
  have hpoint : ∀ s ∈ E, g s ≤ 0 := by
    intro s hs
    have hs' : s ∈ paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ) := hs
    have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s :=
      Real.coe_toNNReal s hs'.2.1
    have ht : s.toNNReal ≤ T := by
      exact_mod_cast (show (((s.toNNReal : ℝ≥0) : ℝ) ≤ (T : ℝ)) from by
        simpa only [hcoe] using hs'.2.2)
    obtain ⟨hpos, hcap⟩ :=
      hloc s.toNNReal ht (by simpa only [hcoe] using hs'.1)
    have hgrad :=
      hw_grad (riskProcess X x D s.toNNReal ω) hpos hcap
    have hdiff : 1 - deriv w (riskProcess X x D s.toNNReal ω) ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) hdiff
  have hAe : ∀ᵐ s ∂ν.restrict E, g s ≤ 0 := by
    filter_upwards [ae_restrict_mem hMeas] with s hs
    exact hpoint s hs
  change (∫ s : ℝ, g s ∂ν.restrict E) ≤ 0
  exact integral_nonpos_of_ae hAe
