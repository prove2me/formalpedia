-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_zero_clock_stopped_compensated_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:05:36.825178+00:00
-- url     : https://prove2.me/submissions/8506a8f8-572a-4ab0-a57b-72698d8ae1d1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, ∀ᵐ p ∂(NX ω), p.1 ≠ 0)
    (ν : Measure ℝ) (T : ℝ≥0)
    (σ : Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ → ℝ) :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
  intro ω hzero
  have hjump :
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hNX ω] with p hp
    have hnot : ¬ p.1 ≤ σ ω := by
      rw [hzero]
      exact not_le.mpr (pos_iff_ne_zero.mpr hp)
    simp [hnot]
  have hcomp :
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
    apply avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
      T (fun t => ∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
    intro t ht
    have hnot : ¬ t ≤ σ ω := by
      rw [hzero]
      exact not_le.mpr (pos_iff_ne_zero.mpr ht)
    simp [hnot]
  rw [hjump, hcomp]
  ring
