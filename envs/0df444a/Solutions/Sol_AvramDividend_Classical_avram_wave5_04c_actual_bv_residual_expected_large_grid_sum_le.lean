-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_expected_large_grid_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:43:51.429118+00:00
-- url     : https://prove2.me/submissions/a5b5836e-4077-4239-9348-f327a7d9f2d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (h : ℝ≥0) (hh : h ≤ 1) (n : ℕ) (hn : (n : ℝ≥0) * h ≤ 1) (M : ℝ) : (∫ ω, ∑ i ∈ Finset.range n, if M < (((((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift - X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) - (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω)) then (((((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift - X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) - (((i : ℝ≥0) * h : ℝ) * X.drift - X.X ((i : ℝ≥0) * h) ω)) else 0 ∂P) ≤ ∫ ω, if M < (((n : ℝ≥0) * h : ℝ) * X.drift - X.X ((n : ℝ≥0) * h) ω) then (((n : ℝ≥0) * h : ℝ) * X.drift - X.X ((n : ℝ≥0) * h) ω) else 0 ∂P := by
  let R : ℝ≥0 → Ω → ℝ :=
    fun t ω => (t : ℝ) * X.drift - X.X t ω
  let F : ℝ → ℝ := fun z => if M < z then z else 0
  let Y : ℕ → Ω → ℝ := fun i ω =>
    R (((i+1 : ℕ) : ℝ≥0) * h) ω - R ((i : ℝ≥0) * h) ω
  have hf : Measurable F := by
    have hs : MeasurableSet {z : ℝ | M < z} := measurableSet_Ioi
    exact Measurable.ite hs measurable_id measurable_const
  have horder (i : ℕ) :
      (i : ℝ≥0) * h ≤ ((i+1 : ℕ) : ℝ≥0) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (by positivity)
  have hstep (i : ℕ) :
      (((i+1 : ℕ) : ℝ≥0) * h) - (i : ℝ≥0) * h = h := by
    simp [Nat.cast_add, add_mul, add_sub_cancel_left]
  have hcells : ∀ i ∈ Finset.range n,
      Integrable (fun ω => F (Y i ω)) P := by
    intro i hi
    have hId0 := actual_levy_drift_deficit_stationary_increment_law X
      ((i : ℝ≥0) * h) (((i+1 : ℕ) : ℝ≥0) * h) (horder i)
    have hId : IdentDistrib (Y i)
        (R ((((i+1 : ℕ) : ℝ≥0) * h) - (i : ℝ≥0) * h)) P P := by
      convert hId0 using 1 <;> funext ω <;> dsimp [Y, R] <;> ring
    have hid := hId.comp hf
    have hright : Integrable (fun ω => F (R h ω)) P := by
      simpa only [R, F] using
        avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
          X hX hBV h hh M
    have hleft := hid.integrable_iff.mpr (by
      simpa only [hstep i, Function.comp_def, R, F] using hright)
    simpa only [Function.comp_def] using hleft
  have hterm : Integrable
      (fun ω => F (R ((n : ℝ≥0) * h) ω)) P := by
    simpa only [R, F] using
      avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
        X hX hBV ((n : ℝ≥0) * h) hn M
  have hsum : Integrable
      (fun ω => ∑ i ∈ Finset.range n, F (Y i ω)) P :=
    integrable_finset_sum _ hcells
  have ha :=
    avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
      X hBV h n M
  have hbound : ∀ᵐ ω ∂P,
      (∑ i ∈ Finset.range n, F (Y i ω)) ≤
        F (R ((n : ℝ≥0) * h) ω) := by
    simpa only [R, F, Y, NNReal.coe_mul] using ha
  change (∫ ω, ∑ i ∈ Finset.range n, F (Y i ω) ∂P) ≤
    ∫ ω, F (R ((n : ℝ≥0) * h) ω) ∂P
  exact integral_mono_ae hsum hterm hbound