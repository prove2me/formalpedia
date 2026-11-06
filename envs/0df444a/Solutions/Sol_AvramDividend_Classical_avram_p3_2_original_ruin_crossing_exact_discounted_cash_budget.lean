-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_ruin_crossing_exact_discounted_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:52:11.390485+00:00
-- url     : https://prove2.me/submissions/e4ca6682-5cb0-4107-8d07-c6c7d40db659

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Full original-X/D discounted grid source inequality through the last strictly pre-ruin cell, using the exact physical crossing index. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
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
    let r : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
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
    0 < τ → ∃ i : ℕ, i < m + 1 ∧ u i < τ ∧
      u (i + 1) = τ ∧
      rightLimit D 0 ω +
        (∑ j ∈ Finset.range i, r (j + 1) * cash j) +
        r i * post i ≤
      w x + (∑ j ∈ Finset.range i, r (j + 1) * source j) +
        ∑ j ∈ Finset.range i, (r (j + 1) - r j) * post j := by
  classical
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun j =>
    min (((min j (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let r : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
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
    u (i + 1) = τ ∧
    rightLimit D 0 ω +
      (∑ j ∈ Finset.range i, r (j + 1) * cash j) +
      r i * post i ≤
    w x + (∑ j ∈ Finset.range i, r (j + 1) * source j) +
      ∑ j ∈ Finset.range i, (r (j + 1) - r j) * post j
  intro hτ
  obtain ⟨k, hk, hfilter, hstrict, hbudget⟩ :=
    avram_p3_2_original_ruin_stopped_exact_strict_prefix_discounted_budget
      X x C hC hxc w hw_cont hw_smooth hw_grad
      D hD hjump ω q hq T m hτ
  obtain ⟨i, hi, hUi, hUi1, hcard⟩ :=
    avram_p3_grid3_original_ruin_stopped_strict_prefix_card_eq_crossing_index
      X x D T m ω hτ
  have hcardk :
      ((Finset.range (m + 1)).filter
        (fun j => u (j + 1) < τ)).card = k := by
    rw [hfilter]
    simp
  change ((Finset.range (m + 1)).filter
    (fun j => u (j + 1) < τ)).card = i at hcard
  have hik : k = i := hcardk.symm.trans hcard
  refine ⟨i, hi, hUi, hUi1, ?_⟩
  simpa only [hik] using hbudget
