-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:18:41.100144+00:00
-- url     : https://prove2.me/submissions/8b4dadc8-17b2-488a-a397-ce6b8c78741d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    E (u n) * V (Y (u n)) +
      (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      V x +
        ∑ i ∈ Finset.range n,
          ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
            E (u i) * (V (Z i) - V (Y (u i)))) := by
  dsimp only
  classical
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  let Y : ℝ≥0 → ℝ := fun t =>
    x + X.X t ω - rightLimit D t ω
  let Z : ℕ → ℝ := fun i =>
    x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
  let cash : ℝ :=
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let A : ℕ → ℝ := fun i =>
    ((E (u (i + 1)) - E (u i)) * V (Y (u (i + 1))) +
      E (u i) * (V (Z i) - V (Y (u i))))
  let B : ℕ → ℝ := fun i =>
    E (u i) * (V (Y (u (i + 1))) - V (Z i))
  have hcontrol :
      cash + (V (Y 0) - V x) +
        (∑ i ∈ Finset.range n, B i) ≤ 0 := by
    have h04 :=
      avram_wave5_04b_positive_cap_original_global_real_signed_stieltjes_grid_nonpos
        X x C hC q hq w V hw_cont hw_smooth hw_grad
          hVtop hVfinite D hD ω u n hu hu0 hPre
    simpa [cash, B, E, Y, Z, X.X_zero] using h04
  have hstep (i : ℕ) :
      A i + B i =
        E (u (i + 1)) * V (Y (u (i + 1))) -
          E (u i) * V (Y (u i)) := by
    dsimp [A, B]
    ring
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, (A i + B i)) =
        E (u k) * V (Y (u k)) -
          E (u 0) * V (Y (u 0)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hstep]
      ring
  have hclock : E (u 0) = 1 := by
    simp [E, hu0]
  have hYzero : Y (u 0) = Y 0 := by
    simp [hu0]
  have hstate := htel n
  rw [Finset.sum_add_distrib, hclock, hYzero] at hstate
  change E (u n) * V (Y (u n)) + cash ≤
    V x + ∑ i ∈ Finset.range n, A i
  linarith
