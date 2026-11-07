-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_positive_deriv_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:07:56.868087+00:00
-- url     : https://prove2.me/submissions/b9dd538e-f6a5-49db-b5ae-9446054e075a

import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hcont : ContinuousOn w (Ici 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ w x)
    (hgrad : ∀ x : ℝ, 0 < x → 1 ≤ deriv w x) :
    MonotoneOn w (Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ w x := by
  have hd : DifferentiableOn ℝ w (interior (Ici (0 : ℝ))) := by
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    exact (hdiff x hxpos).differentiableWithinAt
  have hmono : MonotoneOn w (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcont hd
    intro x hx
    have hxpos : 0 < x := by simpa using hx
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (hgrad x hxpos)
  refine ⟨hmono, ?_⟩
  intro x hx
  exact le_trans hw0 (hmono (by simp) (by simpa using hx) hx)
