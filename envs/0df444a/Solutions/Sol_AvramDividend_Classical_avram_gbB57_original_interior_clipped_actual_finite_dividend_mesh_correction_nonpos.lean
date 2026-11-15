-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB57_original_interior_clipped_actual_finite_dividend_mesh_correction_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:27:39.895792+00:00
-- url     : https://prove2.me/submissions/3d02a2e5-a4ef-440d-8080-edb7b162a7eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z =
      if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i ∈ Finset.range n,
      ((∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  have hstep : u i ≤ u (i + 1) :=
    hu (Nat.le_succ i)
  exact avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
    X x c hc C q hq w V hw_cont hw_smooth hw_grad hV
    D hD ω (u i) (u (i + 1)) hstep
    (hPre i (Finset.mem_range.mp hi))
