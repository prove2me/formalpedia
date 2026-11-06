-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_clipped_arbitrary_nonnegative_weights_positive_lintegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:40:17.242002+00:00
-- url     : https://prove2.me/submissions/12f6336a-72ac-462b-ab8b-4b80f074e5f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every nonnegative, potentially sample-dependent grid weight preserves the
original BV intrinsic nonlinear correction sign. Discount, clock, grid, and
cell count can therefore all be sample-dependent without any R-L1 assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω, Monotone (u ω))
    (n : Ω → ℕ) (a : Ω → ℕ → ℝ)
    (ha : ∀ ω i, 0 ≤ a ω i) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∑ i : Fin (n ω),
        a ω i *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  let G : Ω → ℝ := fun ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    ∑ i : Fin (n ω),
      a ω i *
        (V (riskProcess X x D (v i) ω -
          (R (v (i + 1)) - R (v i))) -
         V (riskProcess X x D (v i) ω))
  have hV : Monotone V :=
    avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
      C hC w V hw_cont hw0 hw_neg hw_smooth hw_grad
      (by intro ht z; simp [V, ht])
      (by intro ht z; simp [V, ht])
  have hR := avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad (0 : ℝ)
  dsimp only at hR ⊢
  have hNonpos : ∀ᵐ ω ∂P, G ω ≤ 0 := by
    filter_upwards [hR] with ω hω
    let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
          else 0).toReal
    have hv : Monotone v := by
      intro i j hij
      exact le_min ((min_le_left _ _).trans (hu ω hij)) (min_le_right _ _)
    change (∑ i : Fin (n ω),
      a ω i * (V (riskProcess X x D (v i) ω -
        (R (v (i + 1)) - R (v i))) -
        V (riskProcess X x D (v i) ω))) ≤ 0
    apply Finset.sum_nonpos
    intro i _
    have hRij : R (v i) ≤ R (v (i + 1)) :=
      hω.1 (hv (Nat.le_succ (i : ℕ)))
    have hdec : V (riskProcess X x D (v i) ω -
        (R (v (i + 1)) - R (v i))) ≤
        V (riskProcess X x D (v i) ω) := by
      apply hV
      exact sub_le_self _ (sub_nonneg.mpr hRij)
    exact mul_nonpos_of_nonneg_of_nonpos (ha ω i) (sub_nonpos.mpr hdec)
  have hZero : (fun ω => ENNReal.ofReal (G ω)) =ᵐ[P]
      (fun _ : Ω => (0 : ℝ≥0∞)) := by
    filter_upwards [hNonpos] with ω hω
    exact ENNReal.ofReal_eq_zero.mpr hω
  calc
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) =
        ∫⁻ _ω : Ω, (0 : ℝ≥0∞) ∂P := lintegral_congr_ae hZero
    _ = 0 := by simp
