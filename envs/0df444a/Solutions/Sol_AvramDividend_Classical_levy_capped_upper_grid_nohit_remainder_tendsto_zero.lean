-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upper_grid_nohit_remainder_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:49:50.958171+00:00
-- url     : https://prove2.me/submissions/385c927f-29c3-4680-83d6-82a15e4c1526

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_discounted_remainder_bound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- The capped upper-grid no-hit mass vanishes as the terminal horizon diverges. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hq : 0 < q) (hroot : X.ψ θ = q)
    (z : ℝ)
    (hT : Tendsto (fun n => ((clock n (m n) : ℝ≥0) : ℝ)) atTop atTop) :
    Tendsto (fun n =>
      ∫ ω, (if ∀ j : ℕ, j ≤ m n → X.X (clock n j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
        Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ)
      else (0 : ℝ)) ∂P) atTop (𝓝 (0 : ℝ)) := by
  have harg : Tendsto
      (fun n => θ * z - ((clock n (m n) : ℝ≥0) : ℝ) * q) atTop atBot := by
    apply tendsto_atBot.2
    intro B
    have hlarge := (tendsto_atTop.1 hT) ((θ * z - B) / q)
    filter_upwards [hlarge] with n hn
    have hmul : θ * z - B ≤ ((clock n (m n) : ℝ≥0) : ℝ) * q := by
      calc
        θ * z - B = ((θ * z - B) / q) * q := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hn (le_of_lt hq)
    linarith
  have hexp : Tendsto
      (fun n => Real.exp (θ * z - ((clock n (m n) : ℝ≥0) : ℝ) * q))
      atTop (𝓝 (0 : ℝ)) := Real.tendsto_exp_atBot.comp harg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hexp
  · intro n
    apply integral_nonneg
    intro ω
    change (0 : ℝ) ≤
      (if ∀ j : ℕ, j ≤ m n → X.X (clock n j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
        Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ)
      else (0 : ℝ))
    by_cases hnone : ∀ j : ℕ, j ≤ m n → X.X (clock n j) ω ≤ z
    · rw [if_pos hnone]
      exact Real.exp_nonneg _
    · rw [if_neg hnone]
  · intro n
    exact levy_capped_upper_grid_nohit_discounted_remainder_bound
      X (clock n) θ q hθ hroot z (m n)
