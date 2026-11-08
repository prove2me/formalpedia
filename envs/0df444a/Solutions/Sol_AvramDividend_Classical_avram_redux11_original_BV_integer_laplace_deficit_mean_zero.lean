-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:24:23.676198+00:00
-- url     : https://prove2.me/submissions/2fc58a4b-ce5e-4b8d-aabc-d099050d8e25

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_path
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_integer_actual_jump_laplace_formula
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
      let R : ℝ≥0 → Ω → ℝ := fun t ω =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
      ∀ n : ℕ, (∫ ω, 1 - Real.exp (-(R (n : ℝ≥0) ω)) ∂P) = 0  := by
  have hpath :=
    avram_p3_a_bvdrift_original_integer_laplace_global_path X hBV 1
      (by norm_num)
      (by
        intro k
        have hcast : ((k : ℝ≥0) : ℝ) = (k : ℝ) := by norm_cast
        simpa only [one_mul, hcast] using
          (avram_redux11_original_integer_actual_jump_laplace_formula X hX hBV k))
  have hraw :=
    avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV
  dsimp only
  intro n
  let J : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
  let R : ℝ≥0 → Ω → ℝ := fun t ω =>
    ((t : ℝ) * X.drift - X.X t ω) - J t ω
  change (∫ ω : Ω, 1 - Real.exp (-(R (n : ℝ≥0) ω)) ∂P) = 0
  have hz :
      (fun ω : Ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) =ᵐ[P]
        (fun _ : Ω => (0 : ℝ)) := by
    filter_upwards [hpath, hraw] with ω hp hr
    have ht := hp (n : ℝ≥0)
    have hj := (hr 0 (n : ℝ≥0) (by positivity)).2
    have hR : R (n : ℝ≥0) ω = 0 := by
      dsimp [R, J]
      rw [ht, ← hj]
      ring
    simp [hR]
  rw [integral_congr_ae hz]
  simp
