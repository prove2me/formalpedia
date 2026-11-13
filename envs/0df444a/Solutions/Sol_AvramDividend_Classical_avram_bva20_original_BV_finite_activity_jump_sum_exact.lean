-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_BV_finite_activity_jump_sum_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:51:07.186137+00:00
-- url     : https://prove2.me/submissions/d1463d76-4a9c-48c6-804d-6cf873d47c41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b20_nostanding_finiteactivity_actual_jump_laplace
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_laplace_global_path
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) * X.drift - X.X t ω =
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by
  have hPath :=
    avram_p3_a_bvdrift_original_integer_laplace_global_path
      X hBV (1 : ℝ) (by norm_num) (by
        intro n
        simpa only [one_mul, NNReal.coe_natCast] using
          (avram_b20_nostanding_finiteactivity_actual_jump_laplace
            X hBV hFinite n))
  have hSum :=
    avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum X hBV
  filter_upwards [hPath, hSum] with ω hω hs
  intro t ht
  have htsum := (hs 0 t (show (0 : ℝ≥0) ≤ t from zero_le)).2
  have hωt := hω t
  rw [htsum] at hωt
  linear_combination -hωt
