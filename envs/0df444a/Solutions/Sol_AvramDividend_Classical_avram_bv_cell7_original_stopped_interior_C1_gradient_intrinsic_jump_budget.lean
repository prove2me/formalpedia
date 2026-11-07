-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:44:17.000562+00:00
-- url     : https://prove2.me/submissions/c1d6c3e8-1421-4d7e-bbb3-644730d4c060

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original pre-right-dividend C1 gradient supplies a genuinely
    nonnegative physical-cell weight for the intrinsic BV drift/jump budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let s : ℕ → Ω → ℝ≥0 := fun i ω =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Y : ℕ → Ω → ℝ := fun i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (s i ω)
    let W : ℕ → Ω → ℝ := fun i ω =>
      if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
        Real.exp (-(q * (s i ω : ℝ))) * deriv w (Y i ω)
      else 0
    ∀ᵐ ω ∂P,
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i ω) (s (i + 1) ω))).map
            (fun v : ℝ≥0 => (v, Δ v)))
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1) ω) ω - X.X (s i ω) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) -
            (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let s : ℕ → Ω → ℝ≥0 := fun i ω =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
  let Y : ℕ → Ω → ℝ := fun i ω => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (s i ω)
  let W : ℕ → Ω → ℝ := fun i ω =>
    if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
      Real.exp (-(q * (s i ω : ℝ))) * deriv w (Y i ω)
    else 0
  have hW : ∀ ω i, 0 ≤ W i ω := by
    intro ω i
    by_cases h : (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C
    · have hder : 0 ≤ deriv w (Y i ω) :=
        le_trans (by norm_num) (hw_grad (Y i ω) h.2.1 h.2.2)
      simp only [W, if_pos h]
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hder
    · simp [W, h]
  simpa only [W, Y, s, τ] using
    (AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_weighted_drift_intrinsic_jump_budget
      X hBV x D T m W hW)
