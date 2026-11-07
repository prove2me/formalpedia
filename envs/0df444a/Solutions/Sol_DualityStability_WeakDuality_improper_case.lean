-- Prove2me | solution 1 for DualityStability.WeakDuality.improper_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:42:00.214799+00:00
-- url     : https://prove2.me/submissions/49fd2edc-46dd-49e0-a22d-7a40b624ea57

import Theorems.Thm_DualityStability_WeakDuality_hull_conjugate_identity

open DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

theorem solution (P : Problem E E' F F')
    (himproper : ¬ Proper P.hull) :
    ∀ y' : F', P.dualMaximand y' = ⊥ := by
  intro y'
  -- h is finite (< +∞) somewhere
  obtain ⟨y1, hy1⟩ := P.g_proper_concave.2.2
  obtain ⟨x0, hx0⟩ := P.f_proper_convex.2.2
  have hz : P.perturbation (P.A x0 - y1) ≠ ⊤ := by
    have hle : P.perturbation (P.A x0 - y1) ≤ P.f x0 - P.g y1 := by
      have := iInf_le (fun x : E => P.f x - P.g (P.A x - (P.A x0 - y1))) x0
      simpa [Problem.perturbation, sub_sub_cancel] using this
    refine ne_top_of_le_ne_top ?_ hle
    rw [← EReal.coe_toReal hx0 (P.f_proper_convex.2.1 x0),
      ← EReal.coe_toReal (P.g_proper_concave.2.1 y1) hy1, ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  have hhull_le : P.hull (P.A x0 - y1) ≤ P.perturbation (P.A x0 - y1) := by
    apply Filter.liminf_le_of_frequently_le'
    rw [Filter.frequently_iff]
    intro U hU
    exact ⟨_, mem_of_mem_nhds hU, le_rfl⟩
  obtain ⟨y0, hy0⟩ : ∃ y0, P.hull y0 = ⊥ := by
    by_contra hcon
    push Not at hcon
    exact himproper ⟨hcon, ⟨_, ne_top_of_le_ne_top hz hhull_le⟩⟩
  have hconj : P.hullConjugate y' = ⊤ := by
    apply eq_top_iff.mpr
    have := le_iSup (fun y : F => (P.pairF.pair y y' : EReal) - P.hull y) y0
    simp only [hy0, EReal.coe_sub_bot] at this
    exact this
  have h := hull_conjugate_identity P y'
  rw [← h.2.2, ← h.2.1, ← h.1, hconj, EReal.neg_top]
