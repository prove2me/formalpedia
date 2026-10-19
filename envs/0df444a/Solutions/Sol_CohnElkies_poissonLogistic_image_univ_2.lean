-- Prove2me | solution 2 for CohnElkies.poissonLogistic_image_univ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:32.04876+00:00
-- url     : https://prove2.me/submissions/ddc10bae-ca0b-4537-aafa-2822754aeccb

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


theorem solution :
    poissonLogistic '' (Set.univ : Set ℝ) = Ioo (0 : ℝ) 1 := by
  have hpos : ∀ u, 0 < poissonLogistic u := fun u => by unfold poissonLogistic; positivity
  have hlt : ∀ u, poissonLogistic u < 1 := fun u => by
    unfold poissonLogistic; rw [div_lt_one (by positivity)]; linarith
  ext y; constructor
  · rintro ⟨u, -, rfl⟩; exact ⟨hpos u, hlt u⟩
  · rintro ⟨h0, h1⟩
    have h1' : (1 - y) ≠ 0 := by linarith
    have h1'' : 0 < 1 - y := by linarith
    refine ⟨Real.log (y / (1 - y)) / Real.pi, trivial, ?_⟩
    unfold poissonLogistic
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.exp_log (div_pos h0 h1'')]
    field_simp
    ring

