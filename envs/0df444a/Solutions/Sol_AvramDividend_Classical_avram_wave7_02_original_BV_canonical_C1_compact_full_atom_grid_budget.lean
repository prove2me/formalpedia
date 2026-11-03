-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:59:47.961966+00:00
-- url     : https://prove2.me/submissions/41fe0e4a-e09d-4493-a975-8cbe1c859034

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Canonical BV cap C1 and zero boundary alone provide the discounted full-atom stopped grid envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
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
    (a b : ℝ) (hab : a < b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
        u 0 = 0 →
        (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
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
  have haMem : a ∈ Icc a b := ⟨le_refl _, le_of_lt hab⟩
  have hbMem : b ∈ Icc a b := ⟨le_of_lt hab, le_refl _⟩
  have ha : 0 ≤ a := le_of_lt (hBand haMem).1
  have hb0 : 0 ≤ b := ha.trans (le_of_lt hab)
  have hbCstrict : ENNReal.ofReal b < C := (hBand hbMem).2
  have hbC : ENNReal.ofReal b ≤ C := le_of_lt hbCstrict
  have hNonneg : ∀ y ∈ Icc a b, 0 ≤ w y := by
    intro y hy
    have hy0 : y ∈ Icc (0 : ℝ) b := ⟨ha.trans hy.1, hy.2⟩
    exact
      avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
        C hC w hw_cont hw0 hw_smooth hw_grad b hb0 hbCstrict y hy0
  exact
    avram_wave7_02_original_BV_automatic_C1_full_stieltjes_discounted_grid_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      hjump a b ha hab hBand hbC q hq hNonneg
