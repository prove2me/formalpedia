-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_compact_negative_uniform_source_mean_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:15:36.672361+00:00
-- url     : https://prove2.me/submissions/d10ba493-db3d-4d10-bd3d-ecb9e55d6b5e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_real_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_uniform_mesh_tendsto_positive_smalltime
import Theorems.Thm_AvramDividend_Classical_avram_p2_k_rate_uniform_grid_algebra_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original Levy compact-negative one-cell expectations recover the genuine horizon-scaled Levy integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      (∫ ω, f (X.X (Real.toNNReal ((T : ℝ) / ((n : ℝ) + 1))) ω) ∂P))
      atTop (𝓝 ((T : ℝ) *
        (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ)))))) := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  let δ : ℕ → ℝ := fun n => (T : ℝ) / ((n : ℝ) + 1)
  let F : ℝ → ℝ := fun h => ∫ ω, f (X.X (Real.toNNReal h) ω) ∂P
  have hδ : Tendsto δ atTop (𝓝[>] (0 : ℝ)) :=
    avram_p2_k_uniform_mesh_tendsto_positive_smalltime (T : ℝ) hTr
  have hδnz (n : ℕ) : δ n ≠ 0 := by
    exact ne_of_gt (div_pos hTr (by positivity))
  have hmesh (n : ℕ) : ((n : ℝ) + 1) * δ n = (T : ℝ) := by
    dsimp [δ]
    field_simp
  have hRateOriginal :=
    avram_p2_i_moment_original_negative_compact_test_real_rate
      X f hf a ε hε hflower hfupper
  have hRate : Tendsto (fun h : ℝ => F h / h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
    apply hRateOriginal.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0 : ℝ) < h := hh
    simp [F, hh', div_eq_mul_inv, mul_comm]
  simpa [δ, F] using
    (avram_p2_k_rate_uniform_grid_algebra_bridge
      δ F (T : ℝ) (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))
      hδ hδnz hmesh hRate)
