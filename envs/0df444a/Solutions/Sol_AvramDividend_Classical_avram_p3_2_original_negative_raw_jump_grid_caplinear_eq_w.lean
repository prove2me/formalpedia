-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_negative_raw_jump_grid_caplinear_eq_w
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T23:43:36.615579+00:00
-- url     : https://prove2.me/submissions/4a8fe453-fde6-4185-b24f-e28f865970cf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_frozen_nonpositive_jump_cap_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- All original negative raw-jump cells leave the cap-linear region
downwards, so the exact discounted nonlinear jump sum uses w itself. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (q : ℝ)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u)
    (hCap : ∀ i : ℕ, i < n →
      C = ⊤ ∨ x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (V ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        V (x + X.X (u i) ω - rightLimit D (u i) ω))) =
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w ((x + X.X (u i) ω - rightLimit D (u i) ω) -
          (∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω))) := by
  intro V
  have hTop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro hc z
    simp [V, hc]
  have hFinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro hc z
    simp [V, hc]
  apply Finset.sum_congr rfl
  intro i hi
  have hmono : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hJ := avram_p3_a_bvdrift_original_raw_negative_jump_tsum_nonnegative
    X ω (u i) (u (i + 1)) hmono
  have hEq := avram_p3_bv_frozen_nonpositive_jump_cap_step
    C w V hTop hFinite
    (x + X.X (u i) ω - rightLimit D (u i) ω)
    (-(∑' v : ℝ≥0, if u i < v ∧ v ≤ u (i + 1) then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
       else 0))
    (hCap i (Finset.mem_range.mp hi)) (neg_nonpos.mpr hJ)
  simpa only [sub_eq_add_neg] using
    congrArg (fun r : ℝ => Real.exp (-(q * (u i : ℝ))) * r) hEq
