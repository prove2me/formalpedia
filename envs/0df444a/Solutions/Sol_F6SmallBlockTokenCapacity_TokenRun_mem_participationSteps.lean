-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:31:15.177814+00:00
-- url     : https://prove2.me/submissions/e78acd97-51c0-445b-9764-ab59aa9e6ace

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (b : B) (i : Fin q) :
    i ∈ R.participationSteps b ↔ b ∈ R.support i := by
  classical
  simp [participationSteps]
end F6SmallBlockTokenCapacity.TokenRun
