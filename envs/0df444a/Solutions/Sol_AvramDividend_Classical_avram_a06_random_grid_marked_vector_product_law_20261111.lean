-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_grid_marked_vector_product_law_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:25:11.149553+00:00
-- url     : https://prove2.me/submissions/6169e35e-67b6-4fa4-9b81-0c79dc1723db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_joint_count_mark_grid_transform_measurable_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_pair_measurable_image_law_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Ω → Fin (n + 1) → ℕ) (Y : Ω → ℕ → ℝ)
    (hN : Measurable N) (hY : Measurable Y)
    (hSeparate : IndepFun N Y P) :
    Measure.map (fun ω => WithLp.toLp 2 (fun i : Fin n =>
      ∑ j ∈ Finset.Ico (N ω i.castSucc) (N ω i.succ), Y ω j)) P =
    Measure.map (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j))
      ((Measure.map N P).prod (Measure.map Y P)) := by
  exact AvramDividend.Classical.avram_a06_independent_pair_measurable_image_law_20261111
    P N Y
    (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j))
    hN hY
    (AvramDividend.Classical.avram_a06_joint_count_mark_grid_transform_measurable_20261111 n)
    hSeparate
