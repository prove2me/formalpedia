-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_positiveclock_truegrid_fullStieltjes_terminal_value_upper_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:36:41.958924+00:00
-- url     : https://prove2.me/submissions/75cd5025-b84f-4e97-a793-607e6abc4b50

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n m : ℕ) (ρ : Ω → ℝ≥0)
    (ω : Ω)
    (hρbound : ρ ω ≤ (n : ℝ≥0))
    (hρstrict : (ρ ω : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let u : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (ρ ω) * V (Y (ρ ω)) +
      (∫⁻ s in Icc (0 : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range (m + 2),
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by
  intro Δ u E Y Z
  have hGrid :
      Monotone u ∧ u 0 = 0 ∧ u (m + 2) = ρ ω := by
    exact avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
      n m (ρ ω) hρbound
  have hPre : ∀ i : ℕ, i < m + 2 →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    right
    have hle : u (i + 1) ≤ ρ ω := min_le_right _ _
    have hle' : (u (i + 1) : ℝ≥0∞) ≤ (ρ ω : ℝ≥0∞) := by
      exact_mod_cast hle
    exact lt_of_le_of_lt hle' hρstrict
  have hCore :=
    avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
      X x C hC q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω u (m + 2) hGrid.1 hGrid.2.1 hPre
  simpa only [hGrid.2.2] using hCore

