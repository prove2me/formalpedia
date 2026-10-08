-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_weighted_cumulative_nnreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:25:31.426836+00:00
-- url     : https://prove2.me/submissions/eba4dc16-fd62-46de-be87-5a08ade6ec9b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_weighted_nnreal_map

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
open AvramDividend.Classical

theorem solution
    (μ : Measure ℝ≥0) [SFinite μ] (a s : ℝ) (hs : 0 < s) :
    let β : Measure ℝ :=
      Measure.map (fun z : ℝ≥0 => (z : ℝ))
        (μ.withDensity
          (fun z : ℝ≥0 =>
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
    (∫⁻ x : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
      ENNReal.ofReal (1 / s) *
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal (Real.exp (-s * (z : ℝ))) *
            ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ))) ∂μ) := by
  let β : Measure ℝ :=
    Measure.map (fun z : ℝ≥0 => (z : ℝ))
      (μ.withDensity
        (fun z : ℝ≥0 =>
          ENNReal.ofReal (1 - Real.exp (-a * (z : ℝ)))))
  have hcoe : Measurable (fun z : ℝ≥0 => (z : ℝ)) := by
    fun_prop
  have hsupp : β (Iio (0 : ℝ)) = 0 := by
    dsimp [β]
    rw [Measure.map_apply hcoe measurableSet_Iio]
    have hpre :
        (fun z : ℝ≥0 => (z : ℝ)) ⁻¹' Iio (0 : ℝ) = ∅ := by
      ext z
      simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge z.2
    rw [hpre]
    simp
  have hcum :=
    positiveLaplace_cumulative_measure β s hs hsupp
  have hmap :=
    positiveLaplace_weighted_nnreal_map μ a s
  dsimp [β] at hcum
  rw [hmap] at hcum
  exact hcum
