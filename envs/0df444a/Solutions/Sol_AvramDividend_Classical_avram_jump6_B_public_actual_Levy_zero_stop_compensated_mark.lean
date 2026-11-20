-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_actual_Levy_zero_stop_compensated_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:06:08.868263+00:00
-- url     : https://prove2.me/submissions/0f79da08-9343-4b2c-8d37-b4cc1f4cde79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time
import Theorems.Thm_AvramDividend_Classical_avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (H : ℝ≥0 → Ω → ℝ → ℝ) :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0)
        ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0
          ∂(X.ν.restrict (Iio (0 : ℝ))))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hNXzero : ∀ ω, ∀ᵐ p ∂(NX ω), p.1 ≠ 0 := by
    intro ω
    have h0 : (NX ω) ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) = 0 :=
      avram_wave5_01_actual_source_jump_measure_zero_initial_time
        X ω Set.univ MeasurableSet.univ
    have hset :
        ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) =
        {p : ℝ≥0 × ℝ | p.1 = 0} := by
      ext p
      simp
    rw [hset] at h0
    have hne : ∀ᵐ p ∂(NX ω), p.1 ≠ 0 := by
      apply ae_iff.mpr
      simpa using h0
    exact hne
  have hfinal :
    ∀ ω, σ ω = 0 →
      (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) -
      (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂(X.ν.restrict (Iio (0 : ℝ))))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
    intro ω hzero
    have hjump :
        (∫ p, (if p.1 ≤ σ ω then H p.1 ω p.2 else 0) ∂(NX ω)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hNXzero ω] with p hp
      have hnot : ¬ p.1 ≤ σ ω := by
        rw [hzero]
        exact not_le.mpr (pos_iff_ne_zero.mpr hp)
      simp [hnot]
    have hcomp :
        (∫ t, (∫ z, if t ≤ σ ω then H t ω z else 0 ∂(X.ν.restrict (Iio (0 : ℝ))))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = 0 := by
      apply avram_bva92_original_mapped_compensator_zero_time_supported_real_integral
        T (fun t => ∫ z, if t ≤ σ ω then H t ω z else 0 ∂(X.ν.restrict (Iio (0 : ℝ))))
      intro t ht
      have hnot : ¬ t ≤ σ ω := by
        rw [hzero]
        exact not_le.mpr (pos_iff_ne_zero.mpr ht)
      simp [hnot]
    rw [hjump, hcomp]
    ring
  simpa only [NX] using hfinal
