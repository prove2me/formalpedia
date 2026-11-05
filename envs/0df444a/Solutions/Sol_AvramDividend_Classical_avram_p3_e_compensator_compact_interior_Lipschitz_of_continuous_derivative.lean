-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_compact_interior_Lipschitz_of_continuous_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:12:42.732236+00:00
-- url     : https://prove2.me/submissions/df2f8f7f-c3c5-43b8-afa5-fe9e96ecb8d4

import Mathlib
open Set
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(w : ℝ → ℝ) (a b : ℝ) (hab : a / 2 ≤ b)
(hdiff : ∀ y ∈ Set.Icc (a / 2) b, DifferentiableAt ℝ w y)
(hcontDeriv : ContinuousOn (deriv w) (Set.Icc (a / 2) b)) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by
  have hnonempty : (Icc (a / 2) b).Nonempty :=
    ⟨a / 2, ⟨le_refl _, hab⟩⟩
  have hcontAbs : ContinuousOn (fun y : ℝ => |deriv w y|) (Icc (a / 2) b) :=
    continuous_abs.comp_continuousOn hcontDeriv
  obtain ⟨u, hu, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (a / 2) b)).exists_isMaxOn
      hnonempty hcontAbs
  refine ⟨|deriv w u|, abs_nonneg _, ?_⟩
  intro x hx y hy
  have hbound : ∀ z ∈ Icc (a / 2) b, ‖deriv w z‖ ≤ |deriv w u| := by
    intro z hz
    simpa [Real.norm_eq_abs] using hmax hz
  have hconv : Convex ℝ (Icc (a / 2) b) := convex_Icc (a / 2) b
  have h := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hy hx
  simpa [Real.norm_eq_abs] using h
