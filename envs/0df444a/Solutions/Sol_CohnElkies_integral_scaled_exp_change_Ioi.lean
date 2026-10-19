-- Prove2me | solution 1 for CohnElkies.integral_scaled_exp_change_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:20.470983+00:00
-- url     : https://prove2.me/submissions/84dc01b3-03e7-48d4-bb72-299b0b8ee76f

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal
namespace CohnElkies
theorem _root_.solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    (∫ r : ℝ in Ioi 0, f r) =
      ∫ v : ℝ, (R * Real.exp v) • f (R * Real.exp v) := by
  let F : ℝ → ℝ := fun v => R * Real.exp v
  have himage : F '' (Set.univ : Set ℝ) = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨v, _, rfl⟩
      exact mul_pos hR (Real.exp_pos v)
    · intro hr
      refine ⟨Real.log (r / R), Set.mem_univ _, ?_⟩
      try dsimp [F]
      rw [Real.exp_log (div_pos hr hR)]
      field_simp
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt F (R * Real.exp x) Set.univ x := by
    intro x _
    exact ((Real.hasDerivAt_exp x).const_mul R).hasDerivWithinAt
  have hinj : Set.InjOn F (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    exact Real.exp_injective (mul_left_cancel₀ hR.ne' hxy)
  have h :=
    integral_image_eq_integral_abs_deriv_smul
      (f := F) (f' := fun x => R * Real.exp x)
      MeasurableSet.univ hderiv hinj f
  simpa [himage, F, abs_of_pos (mul_pos hR (Real.exp_pos _))] using! h
end CohnElkies
