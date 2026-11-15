-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB28_original_interior_caplinear_preruin_weighted_stieltjes_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:13:09.497602+00:00
-- url     : https://prove2.me/submissions/a6fe37d4-b9bc-4e90-a82e-61fac4c8c22f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (N : ℕ)
    (hgrid : ∀ i : ℕ, i < N → u i ≤ u (i + 1))
    (hpre : ∀ i : ℕ, i < N →
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < N → 0 ≤ r i) :
    (∑ i ∈ Finset.range N, r i *
      ((∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hi' : i < N := Finset.mem_range.mp hi
  have hcell :=
    avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
      X x c hc C q hq w V hw_cont hw_smooth hw_grad hV
      D hD ω (u i) (u (i + 1)) (hgrid i hi') (hpre i hi')
  exact mul_nonpos_of_nonneg_of_nonpos (hr i hi') hcell
