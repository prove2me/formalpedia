-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_bv_C1_band_derivative_discounted_payment_mesh_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:46:57.153552+00:00
-- url     : https://prove2.me/submissions/6ac5439f-ef3e-46df-a492-5f32c4f13d9f

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (hPre : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω ∈ Icc a b)
    (htotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (u n (k n)) ω - rightLimit D (u n 0) ω ≤ B)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (u n i : ℝ))) -
          Real.exp (-(q * (u n (i + 1) : ℝ)))) *
          |w (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
            w (x + X.X (u n (i + 1)) ω - rightLimit D (u n (i + 1)) ω)|)
      atTop (𝓝 0) := by
  have hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w hwC1 a b hOpen hBand K hK
  exact avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
    X x D hD ω q hq w (K : ℝ) (by positivity) a b hLip
    u hu k m hm hmesh hPre hPost htotal hmesh0
