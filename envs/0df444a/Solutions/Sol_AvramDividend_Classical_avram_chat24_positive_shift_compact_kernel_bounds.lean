-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_shift_compact_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:23:19.222202+00:00
-- url     : https://prove2.me/submissions/2a9299e8-ecd8-42f3-9507-a6380bd9a8f9

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hc : ContinuousOn w (Ici 0))
    (hn : ∀ y < 0, w y = 0) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  have hsub : Icc (a / 2) b ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_lt_of_le (by linarith) hy.1
  have hdc : ContinuousOn (deriv w) (Ioi 0) :=
    hs.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hdc.mono hsub)
  let L : ℝ≥0 := ⟨max K 0, le_max_right K 0⟩
  have hd (y : ℝ) (hy : y ∈ Icc (a / 2) b) : DifferentiableAt ℝ w y :=
    (hs.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hy))
  have hLip : LipschitzOnWith L w (Icc (a / 2) b) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le hd _ (convex_Icc _ _)
    intro y hy
    exact_mod_cast (hK y hy).trans (le_max_left K 0)
  have hsub0 : Icc (0 : ℝ) b ⊆ Ici 0 := fun _ hy => hy.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hsub0)
  refine ⟨L, max B 0, L.coe_nonneg, le_max_right _ _, ?_, ?_⟩
  · intro u hu v hv
    simpa only [Real.dist_eq] using hLip.dist_le_mul u hu v hv
  · intro v hv
    by_cases hn0 : v < 0
    · rw [hn v hn0, abs_zero]
      exact le_max_right _ _
    · simpa only [Real.norm_eq_abs] using
        (hB v ⟨le_of_not_gt hn0, hv⟩).trans (le_max_left B 0)
