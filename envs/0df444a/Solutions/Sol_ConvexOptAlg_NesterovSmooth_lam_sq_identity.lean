-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.lam_sq_identity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:19:58.620932+00:00
-- url     : https://prove2.me/submissions/884bf993-96fa-4568-9b01-c577bb5f43ba

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

open ConvexOptAlg.NesterovSmooth in
theorem solution (s : ℕ) (hs : 1 ≤ s) :
    lam (s - 1) ^ 2 = lam s ^ 2 - lam s := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [lam]
  have h0 : (0:ℝ) ≤ 1 + 4 * lam t ^ 2 := by positivity
  have hr := Real.sq_sqrt h0
  nlinarith [hr]
