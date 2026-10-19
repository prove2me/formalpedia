-- Prove2me | solution 1 for CohnElkies.poissonLogistic_image_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/0ab37309-189d-4c70-bd27-af5deff5203b

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution :
    poissonLogistic '' (Set.univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨u, _, rfl⟩
    have he : 0 < Real.exp (Real.pi * u) := Real.exp_pos _
    unfold poissonLogistic
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).2
      linarith
  · intro hx
    have hratio : 0 < x / (1 - x) :=
      div_pos hx.1 (sub_pos.mpr hx.2)
    refine ⟨Real.log (x / (1 - x)) / Real.pi,
      Set.mem_univ _, ?_⟩
    unfold poissonLogistic
    rw [mul_div_cancel₀ _ Real.pi_ne_zero,
      Real.exp_log hratio]
    field_simp [(sub_pos.mpr hx.2).ne']
    ring
end CohnElkies
