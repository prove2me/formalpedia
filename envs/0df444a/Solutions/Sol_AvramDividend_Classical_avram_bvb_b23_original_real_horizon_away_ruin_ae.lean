-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_real_horizon_away_ruin_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:13:57.893821+00:00
-- url     : https://prove2.me/submissions/e31b1a95-1a7b-4495-a71e-12ce523fd1e3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva21_original_restricted_real_time_ruin_singleton_null
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

/-- The original finite-horizon real-time measure excludes zero, horizon and ruin time almost everywhere. -/
theorem solution (T : ℝ) (hT : 0 < T) (τ : ℝ≥0∞) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      0 < t ∧ t < T ∧ ENNReal.ofReal t ≠ τ := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Icc 0 T)
  have hneq (r : ℝ) : ∀ᵐ t ∂μ, t ≠ r := by
    rw [ae_iff]
    simpa [μ] using
      (AvramDividend.Classical.avram_bva21_original_restricted_real_time_ruin_singleton_null T r)
  have hmem : ∀ᵐ t ∂μ, t ∈ Icc 0 T :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hmem, hneq 0, hneq T, hneq τ.toReal]
    with t ht htzero hthorizon htruin
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have htT : t < T := lt_of_le_of_ne ht.2 hthorizon
  refine ⟨htpos, htT, ?_⟩
  intro heq
  have hreal := congrArg ENNReal.toReal heq
  exact htruin (by simpa [ENNReal.toReal_ofReal htpos.le] using hreal)
