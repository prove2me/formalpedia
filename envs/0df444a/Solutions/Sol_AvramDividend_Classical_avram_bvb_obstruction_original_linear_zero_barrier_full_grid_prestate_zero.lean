-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_linear_zero_barrier_full_grid_prestate_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:54:54.506183+00:00
-- url     : https://prove2.me/submissions/5481e96d-fea8-43b2-b6f2-be33d247ad9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_unit_drift_zero_barrier_exact_linear_dividends
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_no_right_jump_of_initial_below_barrier
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hWithin : ∀ i ∈ Finset.range (n + 1), u n i ≤ 1) :
    ∀ i ∈ Finset.range (n + 1),
      Function.leftLim
        (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω -
          rightLimit (barrierStrategy X 0 0) t ω)
        (u n i) = 0 := by
  let D := barrierStrategy X 0 0
  have hD : IsAdmissibleLe X 0 (0 : ℝ≥0∞) D := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier X 0 0
        (by norm_num) (by norm_num))
  have hZero : ∀ t : ℝ≥0, t ≤ 1 →
      riskProcess X 0 D t ω = 0 := by
    intro t ht
    exact (avram_bvb_obstruction_original_unit_drift_zero_barrier_exact_linear_dividends
      X ω 1 hDrift hPath t ht).2
  intro i hi
  by_cases hz : u n i = 0
  · rw [hz, avram_p2_a_zero_rate_leftLim_origin_nnreal]
    change (0 : ℝ) + X.X 0 ω - rightLimit D 0 ω = 0
    have hR : rightLimit D 0 ω = D 0 ω :=
      barrierStrategy_no_right_jump_of_initial_below_barrier
        X 0 0 (le_refl 0) ω 0
    rw [hR, X.X_zero ω, hD.1.1.1 ω]
    ring
  · have hPos : 0 < u n i :=
      lt_of_le_of_ne (by positivity) (Ne.symm hz)
    have hnb : (nhdsWithin (u n i) (Iio (u n i))).NeBot :=
      nhdsWithin_Iio_neBot' ⟨(0 : ℝ≥0), hPos⟩ (le_refl (u n i))
    exact avram_bvb24_original_zero_contact_actual_predividend_leftLim_zero
      X 0 0 D hD ω 1 (u n i) (hWithin i hi) hnb hPath hZero
