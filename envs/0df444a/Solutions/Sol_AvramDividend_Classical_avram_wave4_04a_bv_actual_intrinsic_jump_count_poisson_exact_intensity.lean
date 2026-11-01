-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:25:30.25721+00:00
-- url     : https://prove2.me/submissions/6e4997b6-fe30-47f1-85f8-1c6c11e15cce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-! The actual finite-activity BV Lévy jump count has the exact source intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (k : ℕ) :
    P.real {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ENNReal)} =
      Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) *
        ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) ^ k /
          (k.factorial : ℝ) := by
  classical
  let step : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
  let grid : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * step n
  have hnext (n i : ℕ) : grid n (i + 1) = grid n i + step n := by
    simp only [grid, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  have ht (n : ℕ) : Monotone (grid n) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) bot_le
  have hGrid (n : ℕ) (hn : 0 < n) :
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T := by
    have hden : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    have hstep : 0 < step n := div_pos hT hden
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij; exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hstep
    · simp only [grid, Nat.cast_zero, zero_mul]
    · change (n : ℝ≥0) * (T / (n : ℝ≥0)) = T
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ T (ne_of_gt hden)
  have hgap (n i : ℕ) (hi : i < n) :
      (((grid n (i + 1) - grid n i : ℝ≥0) : ℝ)) = (step n : ℝ) := by
    rw [hnext]
    exact congrArg (fun z : ℝ≥0 => (z : ℝ))
      (add_tsub_cancel_left (grid n i) (step n))
  have hDist (n i : ℕ) : dist (grid n i) (grid n (i + 1)) = (step n : ℝ) := by
    rw [hnext, NNReal.dist_eq, NNReal.coe_add]
    have hlin : (grid n i : ℝ) - ((grid n i : ℝ) + (step n : ℝ)) =
        -(step n : ℝ) := by ring
    rw [hlin, abs_neg]
    exact abs_of_nonneg (step n).property
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hWidth : Tendsto (fun n : ℕ => (step n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa [step, NNReal.coe_div, div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv : Tendsto
        (fun n : ℕ => (T : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 ((T : ℝ) * (0 : ℝ))))
  have hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ := by
    intro δ hδ
    have hevent : ∀ᶠ n : ℕ in atTop, (step n : ℝ) < δ := hWidth.eventually (eventually_lt_nhds hδ)
    filter_upwards [hevent] with n hn
    intro i hi; simpa only [hDist] using hn
  have hRate : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - Real.exp (-((step n : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
    simpa [step, NNReal.coe_div, div_eq_mul_inv, mul_assoc,
      mul_comm, mul_left_comm] using
      (avram_wave4_04a_actual_negative_jump_uniform_grid_rare_event_rate
        X hFinite T)
  exact avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_law_from_fine_original_grids
    X hBV hFinite T hT grid ht hGrid hMesh
    (fun n => (step n : ℝ)) hgap
    ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) hRate k
