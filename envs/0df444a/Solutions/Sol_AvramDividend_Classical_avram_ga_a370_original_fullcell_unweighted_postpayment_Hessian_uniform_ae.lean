-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:18:29.704388+00:00
-- url     : https://prove2.me/submissions/5226dc8a-641d-477d-9442-8d00b1b6a153

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω →
          |iteratedDeriv 2 w
            (x + X.X s ω - rightLimit D s ω)| ≤ M := by
  obtain ⟨M,hM,hJet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD w C hTopCap hw ρ j hprefix
  refine ⟨M,hM,?_⟩
  filter_upwards [hJet] with ω hω
  intro m i
  dsimp
  intro hs
  have hBound := (hω _ hs).2.2
  have hEq :
      iteratedDeriv 2 w
        (x + X.X ((i : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          rightLimit D ((i : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) =
      deriv (deriv w)
        (x + X.X ((i : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          rightLimit D ((i : ℝ≥0) *
            ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω) := by
    simp [iteratedDeriv_succ]
  simpa only [hEq] using hBound
