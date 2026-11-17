-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_piecewise_quadratic_cap_smoothness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:51:40.852031+00:00
-- url     : https://prove2.me/submissions/8277259b-40df-41f4-a4c5-864c10f75a0a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
noncomputable section
theorem solution :
    let w : ℝ → ℝ := fun z => if z < 0 then 0 else 2 * z - 4 * z ^ 2
    ContinuousOn w (Ici 0) ∧
      ContDiffOn ℝ 2 w (Ioo 0 (1 / 8 : ℝ)) ∧
      w 0 = 0 ∧ (∀ y : ℝ, y < 0 → w y = 0) := by 
  dsimp
  let p : ℝ → ℝ := fun z => 2 * z - 4 * z ^ 2
  have hpcont : Continuous p := by
    dsimp [p]
    fun_prop
  have hpsmooth : ContDiff ℝ 2 p := by
    dsimp [p]
    fun_prop
  have heq : EqOn (fun z : ℝ =>
      if z < 0 then 0 else 2 * z - 4 * z ^ 2) p (Ici 0) := by
    intro z hz
    have hznonneg : (0 : ℝ) ≤ z := hz
    simp [p, not_lt.mpr hznonneg]
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · exact hpcont.continuousOn.congr heq
  · have heq' : EqOn (fun z : ℝ =>
        if z < 0 then 0 else 2 * z - 4 * z ^ 2) p (Ioo 0 (1 / 8 : ℝ)) := by
      intro z hz
      exact heq (le_of_lt hz.1)
    exact hpsmooth.contDiffOn.congr heq'
  · intro y hy
    simp [hy]
