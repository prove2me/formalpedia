-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_strict_preruin_full_cash_at_true_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:02:19.286657+00:00
-- url     : https://prove2.me/submissions/78726e40-e612-4344-828d-554e2f0cabc5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (m : ℕ) :
    let u : ℕ → ℝ≥0 := fun i =>
      min (((i : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) * t) t
    let E : ℝ≥0 → ℝ := fun s => Real.exp (-(q * (s : ℝ)))
    let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (t) * V (Y (t)) +
      (∫⁻ s in Icc (0 : ℝ) ((t) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range (m + 1),
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by
  have hend :
      min (((((m + 1 : ℕ) : ℝ≥0) /
        ((m + 1 : ℕ) : ℝ≥0)) * t)) t = t := by
    have hpos : 0 < (((m + 1 : ℕ) : ℝ≥0)) := by
      exact_mod_cast Nat.succ_pos m
    have hne : (((m + 1 : ℕ) : ℝ≥0)) ≠ 0 := ne_of_gt hpos
    simpa [hne]
  have h := avram_pj_workerC_true_preruin_uniform_caplinear_full_cash
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω t ht m
  dsimp only at h ⊢
  simpa only [hend] using h
