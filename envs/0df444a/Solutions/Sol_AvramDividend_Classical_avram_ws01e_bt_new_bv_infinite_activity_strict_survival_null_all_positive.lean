-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_bv_infinite_activity_strict_survival_null_all_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:44:53.91776+00:00
-- url     : https://prove2.me/submissions/79e6b14c-20e4-476e-9b17-e4c300721a28

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_mesh_grid_calibration
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound
import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_strict_survival_null_of_mesh_bounds
import Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Order.Filter.Tendsto

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ T : ℝ≥0, 0 < T →
      P {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω} = 0 := by
  intro T hT
  obtain ⟨hd, -⟩ := AvramDividend.Classical.bv_standing_drift_pos X hStanding hBV
  have hνinf : X.ν (Iio (0 : ℝ)) = ⊤ := not_lt_top_iff.mp hInfinite
  set K : ℕ := ⌈2 * X.drift * (T : ℝ)⌉₊ + 1 with hK
  let Nn : ℕ → ℕ := fun n => n + K
  have hNpos : ∀ n, 0 < Nn n := fun n => by simp [Nn, hK]
  have hLarge : ∀ n, 2 * X.drift * (T : ℝ) ≤ (Nn n : ℝ) := by
    intro n
    have h1 := Nat.le_ceil (2 * X.drift * (T : ℝ))
    simp only [Nn, hK]; push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let δ : ℕ → ℝ := fun n => ((T / (Nn n : ℝ≥0) : ℝ≥0) : ℝ)
  let θ : ℕ → ℝ := fun n => 1 / (2 * (X.drift * δ n))
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hδ : ∀ n, δ n = (T : ℝ) / (Nn n : ℝ) := fun n => by simp [δ]
  have hδpos : ∀ n, 0 < δ n := fun n => by
    rw [hδ]; exact div_pos hTr (by exact_mod_cast hNpos n)
  have hθeq : ∀ n, θ n = (Nn n : ℝ) / (2 * X.drift * T) := by
    intro n; simp only [θ]; rw [hδ]
    have : (0 : ℝ) < Nn n := by exact_mod_cast hNpos n
    field_simp
  have hθ : Tendsto θ atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (Nn n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat K)
    have h2 := h1.atTop_div_const (show (0 : ℝ) < 2 * X.drift * T by positivity)
    exact h2.congr fun n => (hθeq n).symm
  refine AvramDividend.Classical.bv_infinite_activity_strict_survival_null_of_mesh_bounds X hBV hνinf T hT
    δ θ (1 / (2 * X.drift)) (4 * X.drift * (T : ℝ)) hθ ?_ ?_
    (AvramDividend.Classical.bv_actual_survival_deficit_integrable X hStanding hBV T) ?_
  · intro n; simp only [θ]
    have := hδpos n
    positivity
  · intro n; simp only [θ]
    have := hδpos n
    field_simp
  · intro n
    exact AvramDividend.Classical.avram_ws01e_bt_new_bv_actual_uniform_mesh_survival_bound X hStanding hBV T hT
      (Nn n) (hNpos n) (hLarge n)
