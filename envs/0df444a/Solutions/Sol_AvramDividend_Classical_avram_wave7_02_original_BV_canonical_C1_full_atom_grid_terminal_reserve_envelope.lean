-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_canonical_C1_full_atom_grid_terminal_reserve_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:07:50.962671+00:00
-- url     : https://prove2.me/submissions/77d4aa56-9f24-4d3f-b726-24bc2f5accb6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Exact original positive-cap BV stopped grid cash and terminal physical reserve envelope, including the zero-time atom. -/
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
            (w 0 + (x + X.X (u n) ω - rightLimit D (u n) ω)) ≤
          w x +
          (∑ i ∈ Finset.range n,
            Real.exp (-(q * (u (i + 1) : ℝ))) *
              (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by
  obtain ⟨L, hL, hGrid⟩ :=
    avram_wave7_02_original_BV_canonical_C1_compact_full_atom_grid_budget
      X hX hBV x D hD C hC w hw_cont hw0 hw_smooth hw_grad
      hjump a b hab hBand q hq
  refine ⟨L, hL, ?_⟩
  have hbMem : b ∈ Icc a b := ⟨le_of_lt hab, le_refl _⟩
  have haMem : a ∈ Icc a b := ⟨le_refl _, le_of_lt hab⟩
  have ha0 : 0 ≤ a := le_of_lt (hBand haMem).1
  have hb0 : 0 ≤ b := ha0.trans (le_of_lt hab)
  have hbC : ENNReal.ofReal b < C := (hBand hbMem).2
  filter_upwards [hGrid] with ω hBudget
  intro u hu hu0 hGridBand n
  let y : ℝ := x + X.X (u n) ω - rightLimit D (u n) ω
  have hyBand : y ∈ Icc a b := hGridBand n
  have hy0 : 0 ≤ y := ha0.trans hyBand.1
  have hyCompact : y ∈ Icc (0 : ℝ) b := ⟨hy0, hyBand.2⟩
  have hGrowth : w 0 + y ≤ w y :=
    avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad b hb0 hbC y hyCompact
  have hWeighted :
      Real.exp (-(q * (u n : ℝ))) * (w 0 + y) ≤
        Real.exp (-(q * (u n : ℝ))) * w y :=
    mul_le_mul_of_nonneg_left hGrowth
      (le_of_lt (Real.exp_pos (-(q * (u n : ℝ)))))
  have hCash := hBudget u hu hu0 hGridBand n
  dsimp [y] at hWeighted
  linarith only [hCash, hWeighted]
