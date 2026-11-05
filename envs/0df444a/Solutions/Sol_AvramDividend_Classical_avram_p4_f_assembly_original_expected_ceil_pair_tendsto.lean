-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_expected_ceil_pair_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:18:02.141145+00:00
-- url     : https://prove2.me/submissions/951c15b2-de5d-4737-ae18-58beced0e739

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_grid_rate_triangle
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 =>
        Nat.ceil ((p.1 : ℝ) * (k : ℝ) / (T : ℝ)) <
          Nat.ceil ((p.2 : ℝ) * (k : ℝ) / (T : ℝ)))).card : ℕ) : ℝ≥0∞)
    let r : ℝ :=
      (((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop
      (𝓝 (ENNReal.ofReal (r ^ 2 / 2))) := by
  intro F A r
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
  have hν : X.ν B < ⊤ := by
    exact avram_p2_a_zero_rate_separated_borel_nu_finite
      X B measurableSet_Iic (1 / ((n : ℝ) + 1))
      (by positivity) (by intro x hx; exact hx)
  let a : ℝ≥0 := (X.ν B).toNNReal
  have ha : (a : ℝ≥0∞) = X.ν B :=
    ENNReal.coe_toNNReal (ne_of_lt hν)
  have haReal : (a : ℝ) = (X.ν B).toReal := by
    have hh := congrArg ENNReal.toReal ha
    simpa only [ENNReal.coe_toReal] using hh
  have hRate (k : ℕ) (hk : 0 < k) :
      (∫⁻ ω, A k ω ∂P) =
        ENNReal.ofReal
          (((k : ℝ) * ((k : ℝ) - 1) / 2) *
            (((T : ℝ) * (X.ν B).toReal) ^ 2 / (k : ℝ) ^ 2)) := by
    let s : Fin k → ℝ≥0 := fun i =>
      ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    obtain ⟨hst, htT, hs, ht⟩ :=
      avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
    have hGrid :=
      avram_leanlevy_bridge_original_ceiling_grid_expected_pair_rate
        X T hT n k hk s t hst htT hs ht
    have hTriangle :=
      avram_p4_f_assembly_original_ennreal_grid_rate_triangle T a k hk
    calc
      (∫⁻ ω, A k ω ∂P) =
        ∑ i : Fin k, ((s i : ℝ≥0) : ℝ≥0∞) * X.ν B *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
            simpa only [A, F, B] using hGrid
      _ = ∑ i : Fin k, ((s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞) *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * (a : ℝ≥0∞)) := by
            rw [ha]
      _ = ENNReal.ofReal
          (((k : ℝ) * ((k : ℝ) - 1) / 2) *
            (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)) := by
            simpa only [s, t] using hTriangle
      _ = ENNReal.ofReal
          (((k : ℝ) * ((k : ℝ) - 1) / 2) *
            (((T : ℝ) * (X.ν B).toReal) ^ 2 / (k : ℝ) ^ 2)) := by
            rw [haReal]
  have hLimit :=
    avram_p4_f_assembly_original_grid_mean_limit_of_exact_rate
      X T hT n hRate
  have hSquare :
      ENNReal.ofReal (r ^ 2 / 2) =
        (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by
    simpa only [r, B, ENNReal.toReal_mul, ENNReal.coe_toReal] using
      (avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
        X T n hν)
  rw [hSquare]
  exact hLimit
