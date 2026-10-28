-- Prove2me | solution 1 for AvramDividend.Classical.infinite_small_jump_moment_implies_infinite_negative_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:16:02.831354+00:00
-- url     : https://prove2.me/submissions/66717564-bc82-4508-8cae-455a5637f3d2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (ν : Measure ℝ)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) = ⊤) :
    ν (Iio (0 : ℝ)) = ⊤ := by
  by_contra h
  have hmass : ν (Ioo (-1 : ℝ) 0) < ⊤ :=
    lt_of_le_of_lt (measure_mono (by
      intro y hy
      exact hy.2)) (lt_top_iff_ne_top.mpr h)
  have hle : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) ≤
      (∫⁻ _y in Ioo (-1 : ℝ) 0, (1 : ENNReal) ∂ν) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hyneg : y < (0 : ℝ) := hy.2
    have hyabs : |y| ≤ 1 := by
      rw [abs_of_neg hyneg]
      linarith [hy.1]
    simpa using ENNReal.ofReal_le_ofReal hyabs
  have htop : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) < ⊤ := by
    have hconst : (∫⁻ _y in Ioo (-1 : ℝ) 0,
        (1 : ENNReal) ∂ν) = ν (Ioo (-1 : ℝ) 0) := by simp
    exact lt_of_le_of_lt hle (hconst ▸ hmass)
  rw [hinf] at htop
  exact (lt_irrefl (⊤ : ENNReal)) htop
