-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_grid_HJB_residual_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:02:37.529018+00:00
-- url     : https://prove2.me/submissions/9db16adf-adb6-4de8-96f5-2c8d29866271

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original BV cell generator drift and actual weighted residual are
    together nonpositive, on the genuine stopped physical grid, a.s. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (T : ℝ≥0) (m : ℕ) :
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
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (m + 1),
        (if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
          Real.exp (-(q * (s i ω : ℝ))) *
            (X.generator w (Y i ω) - q * w (Y i ω)) *
            ((s (i + 1) ω : ℝ) - (s i ω : ℝ))
        else 0)) +
        (∑ i ∈ Finset.range (m + 1),
          W i ω * (R (s i ω) - R (s (i + 1) ω))) ≤ 0 := by
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
  have hBudget :=
    AvramDividend.Classical.avram_bv_cell7_original_stopped_interior_C1_gradient_intrinsic_jump_budget
      X hBV x C D hD w hw_grad q T m
  have hResidual :=
    AvramDividend.Classical.avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
      X hBV x D T m W
  filter_upwards [hBudget, hResidual] with ω hbudget hresidual
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
  let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
    ((Measure.count.restrict
      ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i ω) (s (i + 1) ω))).map
        (fun v : ℝ≥0 => (v, Δ v)))
  have hbud :
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (X.X (s (i + 1) ω) ω - X.X (s i ω) ω)) ≤
      ∑ i ∈ Finset.range (m + 1),
        W i ω * ((((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) -
          (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by
    simpa only [W, Y, s, τ, N, Δ] using hbudget
  have hres :
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (s i ω) - R (s (i + 1) ω))) =
      ∑ i ∈ Finset.range (m + 1),
        W i ω * ((X.X (s (i + 1) ω) ω - X.X (s i ω) ω) -
          (((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) +
          (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by
    simpa only [W, Y, s, τ, J, R, N, Δ] using hresidual
  have hRnonpos :
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (s i ω) - R (s (i + 1) ω))) ≤ 0 := by
    rw [hres]
    calc
      (∑ i ∈ Finset.range (m + 1),
        W i ω * ((X.X (s (i + 1) ω) ω - X.X (s i ω) ω) -
          (((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) +
          (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal)) =
        ∑ i ∈ Finset.range (m + 1),
          (W i ω * (X.X (s (i + 1) ω) ω - X.X (s i ω) ω) -
            W i ω * ((((s (i + 1) ω : ℝ) - (s i ω : ℝ)) * X.drift) -
              (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
      _ ≤ 0 := sub_nonpos.mpr hbud
  have hsmon (i : ℕ) : s i ω ≤ s (i + 1) ω := by
    exact (AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2 (Nat.le_succ i)
  have hGnonpos :
      (∑ i ∈ Finset.range (m + 1),
        (if (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C then
          Real.exp (-(q * (s i ω : ℝ))) *
            (X.generator w (Y i ω) - q * w (Y i ω)) *
            ((s (i + 1) ω : ℝ) - (s i ω : ℝ))
        else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    by_cases h : (s i ω : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Y i ω ∧ ENNReal.ofReal (Y i ω) < C
    · simp only [if_pos h]
      apply mul_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (Real.exp_pos _)) (hw_gen (Y i ω) h.2.1 h.2.2)
      · exact sub_nonneg.mpr (by exact_mod_cast hsmon i)
    · simp [h]
  linarith only [hGnonpos, hRnonpos]
