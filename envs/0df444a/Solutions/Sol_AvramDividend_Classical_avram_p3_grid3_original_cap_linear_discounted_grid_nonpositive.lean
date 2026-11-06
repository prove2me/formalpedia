-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_cap_linear_discounted_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:12:11.526445+00:00
-- url     : https://prove2.me/submissions/f3773107-03d3-43b0-ab48-d40840b46550

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hu : Monotone u)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let cell : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc ((u i : ℝ≥0) : ℝ) ((u (i + 1) : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (u i : ℝ))) *
        (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))
    (∑ i ∈ Finset.range n, cell i) ≤ 0 := by
  classical
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro htop z
    simp [V, htop]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro hnot z
    simp [V, hnot]
  apply Finset.sum_nonpos
  intro i hi
  exact avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω q hq (u i) (u (i + 1))
    (hu (Nat.le_succ i)) (hPre i (Finset.mem_range.mp hi))
