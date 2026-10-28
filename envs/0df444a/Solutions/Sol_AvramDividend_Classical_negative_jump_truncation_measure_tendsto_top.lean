-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_truncation_measure_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:45:07.520882+00:00
-- url     : https://prove2.me/submissions/185e06a1-11e4-4af4-9f50-0a9f70f59674

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finite negative-jump truncation intensities exhaust an infinite negative Lévy measure. -/
theorem solution
    (ν : Measure ℝ)
    (hν : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun n : ℕ => ν (Iic (-(1 / ((n : ℝ) + 1)))))
      atTop (nhds (⊤ : ℝ≥0∞)) := by 
  have hmono : Monotone (fun n : ℕ => Iic (-(1 / ((n : ℝ) + 1)))) := by
    intro m n hmn
    apply Iic_subset_Iic.mpr
    have : (m : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have h0 : (0:ℝ) < m + 1 := by positivity
    have := one_div_le_one_div_of_le h0 this
    linarith
  have hU : (⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1)))) = Iio 0 := by
    ext y
    simp only [mem_iUnion, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨n, hn⟩
      have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hy)
      exact ⟨n, by linarith⟩
  have := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rw [hU, hν] at this
  exact this
