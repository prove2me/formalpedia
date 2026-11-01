-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:40:00.317413+00:00
-- url     : https://prove2.me/submissions/a28a5009-edd3-46c3-bb52-f355ae5f98bb

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_original_residual_finite_range_of_right_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV finite residual range on positive finite horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ S : Finset ℝ, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω ∈ S := by
  let grid : ℕ → ℕ → ℝ≥0 :=
    fun n i => (i : ℝ≥0) / (2 : ℝ≥0) ^ n * T
  have hAlign : ∀ n i : ℕ, grid (n + 1) (2 * i) = grid n i := by
    intro n i
    dsimp [grid]
    simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    field_simp
  have hGridMono : ∀ n, Monotone (grid n) := by
    intro n i j hij
    dsimp [grid]
    gcongr
  have hMesh : ∀ n i : ℕ, i < 2 ^ n →
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ) =
        (T : ℝ) / ((2 ^ n : ℕ) : ℝ)) := by
    intro n i hi
    have hm : grid n i ≤ grid n (i + 1) := by
      dsimp [grid]
      gcongr
      omega
    rw [NNReal.coe_sub hm]
    dsimp [grid]
    simp only [NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_pow, Nat.cast_add, Nat.cast_one]
    push_cast
    field_simp
    ring
  have hRightCover : ∀ t : ℝ≥0, t ≤ T →
      ∃ index : ℕ → ℕ,
        (∀ n, index n ≤ 2 ^ n) ∧
        (∀ n, t ≤ grid n (index n)) ∧
        Tendsto (fun n => grid n (index n)) atTop (nhds t) := by
    intro t ht
    let index : ℕ → ℕ := fun n =>
      Nat.ceil (((t / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
    have hratio : (t / T : ℝ≥0) ≤ 1 := by
      apply (div_le_iff₀ hT).mpr
      simpa using ht
    have hr : (((t / T : ℝ≥0) : ℝ)) ≤ 1 := by exact_mod_cast hratio
    have hi : ∀ n : ℕ, index n ≤ 2 ^ n := by
      intro n
      dsimp [index]
      apply Nat.ceil_le.mpr
      have hp : (0 : ℝ) ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
      have h :
          (((t / T : ℝ≥0) : ℝ)) * (2 : ℝ) ^ n ≤
            (2 : ℝ) ^ n := by nlinarith
      simpa only [NNReal.coe_div, Nat.cast_pow, Nat.cast_ofNat] using h
    have hbase :=
      avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit t T hT ht
    change
      (∀ n, t ≤ (index n : ℝ≥0) / (2 : ℝ≥0) ^ n * T ∧
        (index n : ℝ≥0) / (2 : ℝ≥0) ^ n * T ≤ T) ∧
      Tendsto (fun n => (index n : ℝ≥0) / (2 : ℝ≥0) ^ n * T)
        atTop (nhds t) at hbase
    refine ⟨index, hi, ?_, ?_⟩
    · intro n
      simpa [grid] using (hbase.1 n).1
    · simpa [grid] using hbase.2
  exact
    avram_wave4_04a_bv_original_residual_finite_range_of_right_grid
      X hBV hFinite grid T hAlign hGridMono hMesh hRightCover
