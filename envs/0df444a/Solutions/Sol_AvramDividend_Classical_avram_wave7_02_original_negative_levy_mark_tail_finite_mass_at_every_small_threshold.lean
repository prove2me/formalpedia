-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:32:03.231856+00:00
-- url     : https://prove2.me/submissions/97df4c30-875e-4747-9815-c9b0a09aa7d3

import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical
noncomputable section

/-- The Lévy square-energy condition implies finite physical negative mark
intensity below every fixed negative threshold of size at most one. -/
theorem solution
    (ν : Measure ℝ)
    (hν : (∫⁻ z : ℝ,
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂ν) < ⊤)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    ν (Iic (-δ)) < ⊤ := by
  have hMeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min (1 : ℝ) (z ^ 2))) := by
    fun_prop
  have hδsq : δ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδone)
      (show 0 ≤ 1 + δ by linarith)]
  have hThreshold : ∀ z ∈ Iic (-δ),
      ENNReal.ofReal (δ ^ 2) ≤
        ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) := by
    intro z hz
    have hzle : z ≤ -δ := hz
    have hzneg : 0 ≤ -z - δ := by linarith only [hzle]
    have hzpos : 0 ≤ -z + δ := by linarith only [hzle, hδ]
    have hZsq : δ ^ 2 ≤ z ^ 2 := by
      nlinarith [mul_nonneg hzneg hzpos]
    exact ENNReal.ofReal_le_ofReal (le_min hδsq hZsq)
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ ^ 2) := by
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hδ)
  exact avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
    ν (fun z : ℝ => ENNReal.ofReal (min (1 : ℝ) (z ^ 2)))
    hMeas hν (Iic (-δ)) measurableSet_Iic
    (ENNReal.ofReal (δ ^ 2)) hεpos hThreshold
