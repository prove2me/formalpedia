-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_stopped_C1_sampled_grid_budget_without_free_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:13:26.231944+00:00
-- url     : https://prove2.me/submissions/93820635-23f5-49ad-a733-d19ab7a80fc3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Exact original zero-time atom and C1 finite-grid cash budget with a physical derived slope witness. -/
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
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBandSmooth : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (q : ℝ) (hq : 0 ≤ q) :
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
            ((↑(max K 1 : ℝ≥0) : ℝ) * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) := by
  have hK' : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ max K 1 := by
    intro y hy
    exact (hK y hy).trans (le_max_left K 1)
  have hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ ((max K 1 : ℝ≥0) : ℝ) * |y - z| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w (fun _ => hw_smooth) a b hOpen hBandSmooth
      (max K 1) hK'
  have hL1 : (1 : ℝ) ≤ ((max K 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast (le_max_right K (1 : ℝ≥0))
  exact
    avram_wave7_02_original_BV_initial_atom_discounted_grid_sampled_nonnegative_budget
      X hX hBV x D hD C hC w hw_cont hw_smooth hw_grad hjump
      a b ((max K 1 : ℝ≥0) : ℝ) ha hab hbC hL1 hLip q hq
