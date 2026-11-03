-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_bv_C1_clipped_ruinstopped_payment_mesh_error_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:52:32.467197+00:00
-- url     : https://prove2.me/submissions/5da381e7-e34e-4e2a-9d72-dae11b424db5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hu : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0) (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hPre : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b)
    (hPost : ∀ n i, i < k n →
      x + X.X (min (u n (i + 1)) (τ ω)) ω -
        rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)
    (hmesh0 : Tendsto m atTop (𝓝 0)) :
    Tendsto (fun n =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      ∑ i ∈ Finset.range (k n),
        (Real.exp (-(q * (v i : ℝ))) -
          Real.exp (-(q * (v (i + 1) : ℝ)))) *
          |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
            w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|)
      atTop (𝓝 0) := by
  have hLip : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w hwC1 a b hOpen hBand K hK
  let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
  have hvmono : ∀ n, Monotone (v n) := by
    intro n i j hij
    change min (u n i) (τ ω) ≤ min (u n j) (τ ω)
    exact min_le_min ((hu n) hij) le_rfl
  have hvmesh : ∀ n i, i < k n →
      ((v n (i + 1) : ℝ) - (v n i : ℝ)) ≤ m n := by
    intro n i hi
    simpa [v] using
      (avram_wave6_06_original_clipped_source_cell_mesh_nonexpansive
        (u n) (hu n) i (τ ω) (m n) (hm n) (hmesh n i hi))
  have hvtotal : ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (v n (k n)) ω - rightLimit D (v n 0) ω ≤ B := by
    simpa [v] using
      (avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
        D hD ω τ u k hzero)
  have hvpre : ∀ n i, i < k n →
      x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω ∈ Icc a b := by
    simpa [v] using hPre
  have hvpost : ∀ n i, i < k n →
      x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω ∈ Icc a b := by
    simpa [v] using hPost
  have hlimit :=
    avram_wave6_06_original_local_payment_discount_mesh_error_tendsto_of_path_bound
      X x D hD ω q hq w (K : ℝ) (by positivity) a b hLip
      v hvmono k m hm hvmesh hvpre hvpost hvtotal hmesh0
  simpa [v] using hlimit
