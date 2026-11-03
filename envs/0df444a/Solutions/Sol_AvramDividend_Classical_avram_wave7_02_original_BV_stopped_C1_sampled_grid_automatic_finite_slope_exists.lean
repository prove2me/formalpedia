-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_automatic_finite_slope_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:26:50.769538+00:00
-- url     : https://prove2.me/submissions/2907e499-aaa6-4213-8b2f-5c57abeea950

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact stopped controlled BV C1 sampled grid and initial-atom cash bound with an automatically finite source slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C)
    (hBandSmooth : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      (∀ n, 0 ≤ w (x + X.X (u n) ω - rightLimit D (u n) ω)) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  obtain ⟨K, hK⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
      X hBV C w hw_smooth a b hab hBandSmooth
  refine ⟨((max K 1 : ℝ≥0) : ℝ), ?_, ?_⟩
  · exact_mod_cast (le_max_right K (1 : ℝ≥0))
  · exact
      avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
        X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad hjump
        a b ha hab hbC hOpen hBandSmooth K hK q hq
