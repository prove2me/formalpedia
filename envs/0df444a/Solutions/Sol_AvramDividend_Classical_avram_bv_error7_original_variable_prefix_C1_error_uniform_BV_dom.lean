-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:32:32.333172+00:00
-- url     : https://prove2.me/submissions/404730fc-d6bc-4b27-a9ef-ad2ca2b4ebc9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original BV X/D physical C1 Taylor error is globally
controlled by the intrinsic source mass on a compact band. This
bound does not require every individual grid increment to be small. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      u 0 = 0 → u n ≤ T →
      (∀ i, i < n → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u i) ω - rightLimit D (u i) ω
       let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
       (∀ i, i < n →
         Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
       |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
         (2 * L) * (|X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|)) := by
  filter_upwards
    [avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
      X hBV T] with ω hω
  intro u n h0 hn hmono
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
  let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
  let z : ℕ → ℝ := fun i =>
    x + X.X (u i) ω - rightLimit D (u i) ω
  let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
  change
    (∀ i, i < n → Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
    |∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
      (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)
  intro hCells
  have hVar : (∑ i ∈ Finset.range n, |c i|) ≤
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω| :=
    hω u n h0 hn hmono
  have hCellBound (i : ℕ) (hi : i ∈ Finset.range n) :
      |Real.exp (-(q * (u i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
      (2 * L) * |c i| := by
    have hExp : Real.exp (-(q * (u i : ℝ))) ≤ 1 := by
      calc
        Real.exp (-(q * (u i : ℝ))) ≤ Real.exp 0 :=
          (Real.exp_le_exp).2
            (neg_nonpos.mpr (mul_nonneg hq (by positivity)))
        _ = 1 := Real.exp_zero
    have hTaylor :=
      avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
        w a b L hL hLip hDeriv (z i) (c i)
        (hCells i (Finset.mem_range.mp hi))
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ 1 * |w (z i + c i) - w (z i) -
        deriv w (z i) * c i| :=
          mul_le_mul_of_nonneg_right hExp (abs_nonneg _)
      _ ≤ 1 * ((2 * L) * |c i|) :=
          mul_le_mul_of_nonneg_left hTaylor (by norm_num)
      _ = (2 * L) * |c i| := by ring
  calc
    |∑ i ∈ Finset.range n,
      Real.exp (-(q * (u i : ℝ))) *
        (w (z i + c i) - w (z i) - deriv w (z i) * c i)|
      ≤ ∑ i ∈ Finset.range n,
          |Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (2 * L) * |c i| :=
      Finset.sum_le_sum hCellBound
    _ = (2 * L) * (∑ i ∈ Finset.range n, |c i|) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * L) * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) :=
      mul_le_mul_of_nonneg_left hVar (by positivity)
