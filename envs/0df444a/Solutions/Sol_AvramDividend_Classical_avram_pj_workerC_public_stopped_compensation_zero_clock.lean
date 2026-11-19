-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_public_stopped_compensation_zero_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:39:11.743719+00:00
-- url     : https://prove2.me/submissions/fbd5a15e-b6b1-4629-aa0f-e58da86a7a8a

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
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
  intro ω hσ0
  have hJzero :
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) = 0 := by
    have hAE : (fun p : ℝ≥0 × ℝ =>
        if p.1 ≤ σ ω then H p.1 ω p.2 else 0) =ᵐ[NX ω]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hNX ω] with p hp
      have hpos : 0 < p.1 := pos_iff_ne_zero.mpr hp
      simp [hσ0, not_le.mpr hpos]
    rw [integral_congr_ae hAE]
    simp
  have hBzero :
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂ν)
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
    apply avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
    intro t ht
    have hpos : 0 < t := pos_iff_ne_zero.mpr ht
    simp [hσ0, not_le.mpr hpos]
  rw [hJzero, hBzero]
  norm_num

