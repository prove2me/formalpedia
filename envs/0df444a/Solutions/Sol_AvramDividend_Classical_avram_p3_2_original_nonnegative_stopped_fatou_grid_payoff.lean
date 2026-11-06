-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_nonnegative_stopped_fatou_grid_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:01:06.43822+00:00
-- url     : https://prove2.me/submissions/74719aa1-5c1a-460a-b622-e117ab7e113f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped physical cash-prefix plus the original postpayment
candidate is nonnegative at its exact crossing index, and is bounded by the
physical source increments. This supplies the pointwise sign of a genuine
Fatou-grid payoff, while its signed source still needs expectation control. -/
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
        0 ≤ (∑ j ∈ Finset.range i, cash j) + post i ∧
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
    0 ≤ (∑ j ∈ Finset.range i, cash j) + post i ∧
    rightLimit D 0 ω + (∑ j ∈ Finset.range i, cash j) + post i ≤
      w x + (∑ j ∈ Finset.range i, source j)
  intro hτ
  obtain ⟨i, hi, hUi, hUi1, hGap, hBudget⟩ :=
    avram_p3_2_original_crossing_index_strict_once_discounted_cash_budget
      X x C hC hxc w hw_cont hw_smooth hw_grad
      D hD hjump ω q hq T m hτ
  have hCash : ∀ j : ℕ, 0 ≤ cash j := by
    intro j
    exact ENNReal.toReal_nonneg
  have hSum : 0 ≤ ∑ j ∈ Finset.range i, cash j := by
    exact Finset.sum_nonneg (by intro j hj; exact hCash j)
  have hPost : 0 ≤ post i :=
    avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
      X w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD ω (u i)
  exact ⟨i, hi, hUi, hUi1, hGap, add_nonneg hSum hPost, hBudget⟩
