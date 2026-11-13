-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a32_compact_translation_vanishing_radius
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:40:03.290859+00:00
-- url     : https://prove2.me/submissions/ff653745-2774-4d91-8ac3-41d347000b7f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a b r : ℝ) (hr : 0 < r)
    (hw : ContinuousOn w (Set.Icc (a - r) (b + r)))
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (y m + δ m) - w (y m))
      atTop (nhds (0 : ℝ)) := by
  have hUC : UniformContinuousOn w (Set.Icc (a - r) (b + r)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hWη⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) ε hε
  have hmin : 0 < min η r := lt_min hη hr
  have hev : ∀ᶠ m : ℕ in atTop, dist (δ m) 0 < min η r :=
    (Metric.tendsto_nhds.mp hδ) (min η r) hmin
  filter_upwards [hev] with m hm
  have hδabs : |δ m| < min η r := by simpa [Real.dist_eq] using hm
  have hδr : |δ m| < r := lt_of_lt_of_le hδabs (min_le_right _ _)
  have hδη : |δ m| < η := lt_of_lt_of_le hδabs (min_le_left _ _)
  obtain ⟨hδlo, hδhi⟩ := abs_lt.mp hδr
  obtain ⟨hylo, hyhi⟩ := hy m
  have hYwide : y m ∈ Set.Icc (a - r) (b + r) := by
    constructor <;> linarith
  have hZwide : y m + δ m ∈ Set.Icc (a - r) (b + r) := by
    constructor <;> linarith
  have hdist : dist (y m + δ m) (y m) < η := by
    simpa [Real.dist_eq, add_sub_cancel_left] using hδη
  have hwε := hWη (y m + δ m) hZwide (y m) hYwide hdist
  simpa [Real.dist_eq] using hwε
