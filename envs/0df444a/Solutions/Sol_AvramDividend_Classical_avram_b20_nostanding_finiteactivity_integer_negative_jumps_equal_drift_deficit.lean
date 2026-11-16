-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_nostanding_finiteactivity_integer_negative_jumps_equal_drift_deficit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:42:31.24532+00:00
-- url     : https://prove2.me/submissions/604112ae-4983-4e8e-8393-b965e1953a63

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_jump_drift_deficit_telescope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) = (n : ℝ) * X.drift - X.X (n : ℝ≥0) ω := by
  rw [ae_all_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    filter_upwards [] with ω
    have hh : ∀ v : ℝ≥0, ¬ (0 < v ∧ v ≤ 0) := by
      intro v hv
      exact not_lt_of_ge hv.2 hv.1
    simp only [X.X_zero, Nat.cast_zero, zero_mul, sub_zero, hh, ite_false]
    simp
  · have ht : (0 : ℝ≥0) < (n : ℝ≥0) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hf := avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite (n : ℝ≥0) ht
    have hflat := avram_wave4_04a_bv_actual_no_jump_interval_is_drift_only
      X hBV hFinite (n : ℝ≥0) ht
    have hsum := avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
      X hBV
    filter_upwards [hf, hflat, hsum] with ω hfω hflatω hsumω
    have hFiniteTime : Set.Finite {t : ℝ≥0 |
        0 < t ∧ t ≤ (n : ℝ≥0) ∧
          X.X t ω - Function.leftLim (fun z => X.X z ω) t ≠ 0} := by
      simpa only [and_left_comm, and_assoc, and_comm] using hfω
    have hFlatTime : ∀ s t : ℝ≥0, s ≤ t → t ≤ (n : ℝ≥0) →
        (∀ u ∈ Ioc s t,
          X.X u ω - Function.leftLim (fun v => X.X v ω) u = 0) →
        (t : ℝ) * X.drift - X.X t ω =
          (s : ℝ) * X.drift - X.X s ω :=
      hflatω
    have hRaw := avram_bv_finite_jump_drift_deficit_telescope
      (fun t : ℝ≥0 => X.X t ω) X.drift (n : ℝ≥0)
      (X.X_zero ω) hFiniteTime hFlatTime
    exact (hsumω 0 (n : ℝ≥0) zero_le).2.trans (by simpa using hRaw)
