-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_joint_count_mark_grid_transform_measurable_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:18:20.09487+00:00
-- url     : https://prove2.me/submissions/22bda4e8-d533-496f-a2d5-beda3e69b33c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    (n : ℕ) :
    Measurable (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)) := by
  apply measurable_from_prod_countable_right
  intro m
  have hPi : Measurable (fun ys : ℕ → ℝ => fun i : Fin n =>
      ∑ j ∈ Finset.Ico (m i.castSucc) (m i.succ), ys j) := by
    apply measurable_pi_iff.mpr
    intro i
    exact Finset.measurable_sum
      (Finset.Ico (m i.castSucc) (m i.succ))
      (fun j _ => measurable_pi_apply j)
  exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp hPi
