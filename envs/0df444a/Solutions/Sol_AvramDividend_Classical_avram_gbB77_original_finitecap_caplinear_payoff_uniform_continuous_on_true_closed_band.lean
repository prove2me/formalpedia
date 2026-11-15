-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:32:22.9805+00:00
-- url     : https://prove2.me/submissions/453e1a02-bf12-4eec-95a9-950fe485a5bd

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (b K : ℝ) (hb : 0 ≤ b) :
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    UniformContinuousOn V (Icc 0 K) := by
  change UniformContinuousOn
    (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
    (Icc 0 K)
  apply isCompact_Icc.uniformContinuousOn_of_continuous
  apply ContinuousOn.if
  · intro y hy
    have hfront : y ∈ frontier (Iic b) := hy.2
    rw [frontier_Iic] at hfront
    have hyb : y = b := by simpa using hfront
    subst y
    simp
  · exact hw_cont.mono (by
      intro y hy
      exact hy.1.1)
  · fun_prop
