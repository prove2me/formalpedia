-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_nonnegative_initial_inclusive_fatou_grid_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:06:30.188008+00:00
-- url     : https://prove2.me/submissions/7a713b14-0905-48f5-bfee-75588da2c54a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The initial right-payment atom, original strict discounted cash prefix
and actual postpayment w reserve form a nonnegative finite stopped payoff,
bounded by w(x) plus the source increments at the exact crossing index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (m : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    0 < τ →
      ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        τ - u i ≤ T / (m + 1) ∧
        0 ≤ rightLimit D 0 ω + (∑ j ∈ Finset.range i, cash j) + post i ∧
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range i, cash j) + post i ≤
          w x + (∑ j ∈ Finset.range i, source j) := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let cash : ℕ → ℝ := fun i =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
  let post : ℕ → ℝ := fun i =>
    w (x + X.X (u i) ω - rightLimit D (u i) ω)
  let source : ℕ → ℝ := fun i =>
    V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
    V (x + X.X (u i) ω - rightLimit D (u i) ω)
  change 0 < τ → ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
    u (i + 1) = τ ∧ τ - u i ≤ T / (m + 1) ∧
    0 ≤ rightLimit D 0 ω + (∑ j ∈ Finset.range i, cash j) + post i ∧
    rightLimit D 0 ω + (∑ j ∈ Finset.range i, cash j) + post i ≤
      w x + (∑ j ∈ Finset.range i, source j)
  intro hτ
  obtain ⟨i, hi, hUi, hUi1, hGap, hNonnegative, hBudget⟩ :=
    avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
      X x hx C hC hxc w hw_cont hw0 hw_neg hw_smooth hw_grad
      D hD hjump ω q hq T m hτ
  have hInitial : 0 ≤ rightLimit D 0 ω :=
    (avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
      X x D hD.1 ω).1
  refine ⟨i, hi, hUi, hUi1, hGap, ?_, hBudget⟩
  linarith
