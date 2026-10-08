-- Prove2me | solution 1 for AvramDividend.Classical.deriv_bounded_on_compact_of_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:25:23.937151+00:00
-- url     : https://prove2.me/submissions/ef6b2fc3-2dce-42a9-b6b0-8c4b1b51056f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (W : ℝ → ℝ) (a l u : ℝ)
    (hlu : l < u) (hsub : Icc l u ⊆ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l u, |deriv W x| ≤ C := by
  have hC2K : ContDiffOn ℝ 2 W (Icc l u) := hC2.mono hsub
  have huniq : UniqueDiffOn ℝ (Icc l u) :=
    uniqueDiffOn_Icc hlu
  have hcont :
      ContinuousOn
        (fun z => ‖iteratedDerivWithin 1 W (Icc l u) z‖)
        (Icc l u) := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      hC2K (by norm_num) huniq).norm
  have hKne : (Icc l u).Nonempty := by
    refine ⟨l, ?_⟩
    exact ⟨le_rfl, hlu.le⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ Icc l u, ∀ z ∈ Icc l u,
        ‖iteratedDerivWithin 1 W (Icc l u) z‖ ≤
          ‖iteratedDerivWithin 1 W (Icc l u) zM‖ :=
    isCompact_Icc.exists_isMaxOn hKne hcont
  let C : ℝ := ‖iteratedDerivWithin 1 W (Icc l u) zM‖
  refine ⟨C, norm_nonneg _, ?_⟩
  intro x hx
  have hxC1 : ContDiffAt ℝ 1 W x :=
    (hC2.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).of_le
      (by norm_num)
  have hxEq :
      iteratedDerivWithin 1 W (Icc l u) x = deriv W x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hxC1 hx]
    simp
  have hn : ‖deriv W x‖ ≤ C := by
    rw [← hxEq]
    exact hmax x hx
  simpa only [Real.norm_eq_abs] using hn
