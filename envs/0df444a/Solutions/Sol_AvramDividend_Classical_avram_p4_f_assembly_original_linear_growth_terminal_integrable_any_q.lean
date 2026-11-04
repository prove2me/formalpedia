-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_terminal_integrable_any_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:38:07.030742+00:00
-- url     : https://prove2.me/submissions/3cff9253-ce8f-4889-b0f4-39eb2e3f3dd9

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original stopped UBV terminal L1 under a valid linear source candidate bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (θ B L K : ℝ) (hθ : 0 ≤ θ)
    (hK : 0 ≤ K) (hB : B ≤ K) (hL : L ≤ K * θ)
    (hlinear : ∀ y : ℝ, 0 ≤ y → w y ≤ B + L * y) :
    Integrable Term P := by
  have hneg : ∀ y : ℝ, y < 0 → w y ≤ 0 := by
    intro y hy
    simp [hw_neg y hy]
  have hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y) :=
    avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
      w B L K θ hθ hK hB hL hneg hlinear
  have hNonneg : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q τ W Term hW hTerm
  exact avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
    X C x D hD τ W Term hτmeas hτstop H hbound hW
    w q θ K hθ hK hwGrowth
    hTerm hTermMeas (Filter.Eventually.of_forall hNonneg)


