-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_normalized_tail_le_two_terminal_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:35:14.000196+00:00
-- url     : https://prove2.me/submissions/0101e49d-9bc1-4b34-9af7-1d5074ce86fc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation) (h : ℝ≥0)
    (hhpos : 0 < h) (hhhalf : h ≤ (1 / 2 : ℝ≥0)) (M : ℝ) :
    (h : ℝ)⁻¹ * (∫ ω, if M < (h : ℝ) * X.drift - X.X h ω then (h : ℝ) * X.drift - X.X h ω else 0 ∂P)
      ≤ 2 * (∫ ω, if M < (1 : ℝ) * X.drift - X.X 1 ω then (1 : ℝ) * X.drift - X.X 1 ω else 0 ∂P) := by
  let R : ℝ≥0 → Ω → ℝ := fun t ω => (t : ℝ) * X.drift - X.X t ω
  let F : ℝ → ℝ := fun z => if M < z then z else 0
  have hposR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hhpos
  have hhalfR : (h : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hhhalf
  have hfloor (u : ℝ) (hu : 0 < u) (hhalfu : u ≤ 1 / 2) :
      ∃ n : ℕ, (1 / 2 : ℝ) ≤ (n : ℝ) * u ∧ (n : ℝ) * u ≤ 1 := by
    let n : ℕ := ⌊1 / u⌋₊
    have hp : 0 ≤ (1 / u : ℝ) := by positivity
    have hflo : (n : ℝ) ≤ 1 / u := Nat.floor_le hp
    have hfhi : 1 / u < (n : ℝ) + 1 := Nat.lt_floor_add_one (1 / u)
    have hcancel : (1 / u) * u = (1 : ℝ) := by
      field_simp
    have hlo : 1 - u < (n : ℝ) * u := by
      have hm := mul_lt_mul_of_pos_right hfhi hu
      nlinarith
    have hhi : (n : ℝ) * u ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_right hflo (le_of_lt hu)
      nlinarith
    refine ⟨n, ?_, hhi⟩
    linarith
  obtain ⟨n, hnlow, hnup⟩ := hfloor (h : ℝ) hposR hhalfR
  have hnh : (n : ℝ≥0) * h ≤ 1 := by exact_mod_cast hnup
  have hh1 : h ≤ 1 := le_trans hhhalf (by norm_num)
  have hcell : (n : ℝ) * (∫ ω, F (R h ω) ∂P) ≤
      ∫ ω, F (R ((n : ℝ≥0) * h) ω) ∂P := by
    simpa only [R, F, NNReal.coe_mul] using
      avram_wave5_04c_actual_bv_residual_uniform_grid_one_cell_tail_bound
        X hX hBV h hh1 n hnh M
  have hterm : (∫ ω, F (R ((n : ℝ≥0) * h) ω) ∂P) ≤
      ∫ ω, F (R 1 ω) ∂P := by
    simpa only [R, F, NNReal.coe_one] using
      avram_wave5_04c_actual_bv_residual_tail_expected_monotone_upto_one
        X hX hBV ((n : ℝ≥0) * h) hnh M
  have hnonneg : 0 ≤ (∫ ω, F (R h ω) ∂P) := by
    apply integral_nonneg_of_ae
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hm
    have hr : 0 ≤ R h ω := by
      simpa [R, X.X_zero] using
        hm (show (0 : ℝ≥0) ≤ h from bot_le)
    by_cases hcut : M < R h ω
    · simpa [F, hcut] using hr
    · simp [F, hcut]
  have hscale : (h : ℝ)⁻¹ ≤ 2 * (n : ℝ) := by
    by_contra hnot
    have hbad : 2 * (n : ℝ) < (h : ℝ)⁻¹ := lt_of_not_ge hnot
    have hp := mul_lt_mul_of_pos_right hbad hposR
    have hc : (h : ℝ)⁻¹ * (h : ℝ) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hposR)
    nlinarith
  change (h : ℝ)⁻¹ * (∫ ω, F (R h ω) ∂P) ≤
    2 * (∫ ω, F (R 1 ω) ∂P)
  calc
    (h : ℝ)⁻¹ * (∫ ω, F (R h ω) ∂P) ≤
        (2 * (n : ℝ)) * (∫ ω, F (R h ω) ∂P) :=
          mul_le_mul_of_nonneg_right hscale hnonneg
    _ = 2 * ((n : ℝ) * (∫ ω, F (R h ω) ∂P)) := by ring
    _ ≤ 2 * (∫ ω, F (R ((n : ℝ≥0) * h) ω) ∂P) :=
      mul_le_mul_of_nonneg_left hcell (by norm_num)
    _ ≤ 2 * (∫ ω, F (R 1 ω) ∂P) :=
      mul_le_mul_of_nonneg_left hterm (by norm_num)