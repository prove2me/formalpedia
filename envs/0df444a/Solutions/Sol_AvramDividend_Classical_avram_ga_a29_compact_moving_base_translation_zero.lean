-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a29_compact_moving_base_translation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:57:48.655875+00:00
-- url     : https://prove2.me/submissions/193a5181-12f1-40f3-8bf0-c2a1be1c145a

import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hw : ContinuousOn w (Set.Icc (a - 1) (b + 1)))
    (y δ : ℕ → ℝ) (hy : ∀ m, y m ∈ Set.Icc a b)
    (hδ : Tendsto δ atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => w (y m + δ m) - w (y m))
      atTop (nhds (0 : ℝ)) := by
  have hUC : UniformContinuousOn w (Set.Icc (a - 1) (b + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hWη⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) ε hε
  have hsmall : 0 < min η 1 := lt_min hη zero_lt_one
  have hev : ∀ᶠ m : ℕ in atTop, dist (δ m) 0 < min η 1 :=
    (Metric.tendsto_nhds.mp hδ) (min η 1) hsmall
  filter_upwards [hev] with m hm
  have hδabs : |δ m| < min η 1 := by simpa [Real.dist_eq] using hm
  have hδlt : |δ m| < 1 := lt_of_lt_of_le hδabs (min_le_right _ _)
  have hδeta : |δ m| < η := lt_of_lt_of_le hδabs (min_le_left _ _)
  have hδbounds := abs_lt.mp hδlt
  obtain ⟨hya, hyb⟩ := hy m
  have hywide : y m ∈ Set.Icc (a - 1) (b + 1) := by
    constructor <;> linarith
  have hzwide : y m + δ m ∈ Set.Icc (a - 1) (b + 1) := by
    constructor <;> linarith
  have hdist : dist (y m + δ m) (y m) < η := by
    simpa [Real.dist_eq, add_sub_cancel_left] using hδeta
  have hout := hWη (y m + δ m) hzwide (y m) hywide hdist
  simpa [Real.dist_eq] using hout
