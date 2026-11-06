-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_full_stopped_cash_single_contact_mesh_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:06:59.435697+00:00
-- url     : https://prove2.me/submissions/a042910c-861f-406e-a708-1d53bfb4f789

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine full stopped cash is bounded by physical source and one
contact-cell cash term, whose time interval has vanishing mesh length. -/
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
      ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
        i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
        τ - u i ≤ T / (m + 1) ∧
        rightLimit D 0 ω +
          (∑ j ∈ Finset.range (m + 1), cash j) + post k ≤
        w x + (∑ j ∈ Finset.range k, source j) + cash i := by
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
  change 0 < τ → ∃ k i : ℕ, k ≤ m + 1 ∧ u k < τ ∧
    i < m + 1 ∧ u i < τ ∧ u (i + 1) = τ ∧
    τ - u i ≤ T / (m + 1) ∧
    rightLimit D 0 ω +
      (∑ j ∈ Finset.range (m + 1), cash j) + post k ≤
    w x + (∑ j ∈ Finset.range k, source j) + cash i
  intro hτ
  obtain ⟨k, hk, hUk, hBudget⟩ :=
    avram_p3_grid4_original_full_stopped_cash_plus_contact_error_budget
      X x C hC hxc w hw_cont hw_smooth hw_grad
      D hD hjump ω q hq T m hτ
  obtain ⟨i, hi, hUi, hUi1, hFilter⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_tau_boundary_filter_singleton
      X x D T m ω hτ
  obtain ⟨j, hj, hUj, hUj1, hGap⟩ :=
    avram_p3_grid3_original_ruin_stopped_positive_strict_prefix_mesh_gap
      X x D T m ω hτ
  have hjmem :
      j ∈ (Finset.range (m + 1)).filter
        (fun l => u l < τ ∧ u (l + 1) = τ) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ⟨hUj, hUj1⟩⟩
  rw [hFilter] at hjmem
  have hji : j = i := by simpa only [Finset.mem_singleton] using hjmem
  have hGapI : τ - u i ≤ T / (m + 1) := by simpa only [hji] using hGap
  have hSum :
      (∑ j ∈ (Finset.range (m + 1)).filter
        (fun l => u l < τ ∧ u (l + 1) = τ), cash j) = cash i := by
    rw [hFilter]
    simp
  refine ⟨k, i, hk, hUk, hi, hUi, hUi1, hGapI, ?_⟩
  change rightLimit D 0 ω +
      (∑ j ∈ Finset.range (m + 1), cash j) + post k ≤
    w x + (∑ j ∈ Finset.range k, source j) +
      (∑ j ∈ (Finset.range (m + 1)).filter
        (fun l => u l < τ ∧ u (l + 1) = τ), cash j) at hBudget
  rw [hSum] at hBudget
  exact hBudget
