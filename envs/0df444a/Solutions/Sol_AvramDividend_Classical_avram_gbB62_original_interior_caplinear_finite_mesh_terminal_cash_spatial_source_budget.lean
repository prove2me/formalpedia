-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB62_original_interior_caplinear_finite_mesh_terminal_cash_spatial_source_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:00:58.613073+00:00
-- url     : https://prove2.me/submissions/8ca15988-8922-43db-83b3-ba5c6ab42d7f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
import Theorems.Thm_AvramDividend_Classical_avram_gbB61_finite_mesh_postpayment_potential_cash_telescope
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
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ c →
      t - s ≤ w t - w s)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (hPre : ∀ i < n, u (i + 1) = 0 ∨
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (hu0 : u 0 = 0) :
    let Y : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let Z : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
    let Cash : ℕ → ℝ := fun i =>
      (∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + Y n + (Finset.sum (Finset.range n) (fun i => Cash i)) ≤
      V x + (Finset.sum (Finset.range n) (fun i => Z i - Y i)) := by
  let Y : ℕ → ℝ := fun i =>
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  let Z : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)
  let Cash : ℕ → ℝ := fun i =>
    (∫⁻ s in Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  change rightLimit D 0 ω + Y n + (Finset.sum (Finset.range n) (fun i => Cash i)) ≤
    V x + (Finset.sum (Finset.range n) (fun i => Z i - Y i))
  have hBudget :=
    avram_gbB60_original_interior_clipped_finite_mesh_cash_and_initial_atom_budget
      X x c hc C q hq w V hw_cont hw_smooth hw_grad hV hsec
      D hD ω u hu n hPre
  have hY0 : Y 0 = V (x - rightLimit D 0 ω) := by
    simp only [Y, hu0, X.X_zero, add_zero]
  have hGrid :
      rightLimit D 0 ω + Y 0 +
        (Finset.sum (Finset.range n) (fun i => Cash i + Y (i + 1) - Z i)) ≤ V x := by
    rw [hY0]
    simpa only [Cash, Y, Z] using hBudget
  exact avram_gbB61_finite_mesh_postpayment_potential_cash_telescope
    Y Z Cash (rightLimit D 0 ω) (V x) n hGrid
