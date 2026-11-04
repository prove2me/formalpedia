-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_stopped_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:30:49.485611+00:00
-- url     : https://prove2.me/submissions/b44ae60d-7382-4996-a475-36e16cdd9c0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
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
    (θ B L K : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
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
  exact avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
    X C x D hD τ W Term hτmeas hτstop H hbound hW
    w q θ K hθ hψ hK hwGrowth
    hTerm hTermMeas (Filter.Eventually.of_forall hNonneg)