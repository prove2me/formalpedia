-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_automatic_C1_grid_sampled_nonnegative_full_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:07:03.07349+00:00
-- url     : https://prove2.me/submissions/48c02ab4-7110-4e11-996e-bddbee60163c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- Original BV C1 compact interior provides sampled-positive complete discounted grid. -/
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
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hbC : ENNReal.ofReal b ≤ C)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
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
  obtain ⟨L₀, hL₀, hLip₀⟩ :=
    avram_wave6_chat09_original_bv_ENNReal_cap_autoopen_local_C1_lipschitz
      X hBV w C a b hab hBand (fun _ => hw_smooth)
  let L : ℝ := max 1 L₀
  have hLone : 1 ≤ L := le_max_left 1 L₀
  have hLip :
      ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
        |w y - w z| ≤ L * |y - z| := by
    intro y hy z hz
    exact (hLip₀ y hy z hz).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 L₀)
        (abs_nonneg (y - z)))
  refine ⟨L, hLone, ?_⟩
  exact
    avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad
      hjump a b L ha (le_of_lt hab) hbC hLone hLip q hq