-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_uniform_all_stopped_finite_prefix_weighted_R_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:54:00.879954+00:00
-- url     : https://prove2.me/submissions/48e5db11-2003-4307-af6e-4dd011a05197

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One original-BV full-measure event handles every stopped physical finite
prefix and every nonnegative cell weighting, even with arbitrary grid tail. -/
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
      ENNReal.ofReal z < C → 1 ≤ deriv w z) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∀ (τ : ℝ≥0) (u : ℕ → ℝ≥0) (n : ℕ)
        (hu : ∀ i, i < n → u i ≤ u (i + 1))
        (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i),
        let v : ℕ → ℝ≥0 := fun j => min (u (min j n)) τ
        (∑ i : Fin n,
          a i *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by
  have h := avram_p3_2_original_uniform_all_nonnegative_grid_weights_nonlinear_R_nonpos
    X hBV x D w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
  dsimp only at h ⊢
  filter_upwards [h] with ω hω
  intro τ u n hu a ha
  let u' : ℕ → ℝ≥0 := fun j => u (min j n)
  have hMonotone : Monotone u' := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa [u', Nat.min_eq_left (Nat.le_of_lt hi),
        Nat.min_eq_left (Nat.succ_le_of_lt hi)] using hu i hi
    · have hni : n ≤ i := Nat.le_of_not_gt hi
      simp [u', Nat.min_eq_right hni,
        Nat.min_eq_right (hni.trans (Nat.le_succ i))]
  let v : ℕ → ℝ≥0 := fun j => min (u' j) τ
  have hv : Monotone v := by
    intro i j hij
    exact le_min ((min_le_left _ _).trans (hMonotone hij))
      (min_le_right _ _)
  exact hω v hv n a ha
