-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.rank_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:25:02.998157+00:00
-- url     : https://prove2.me/submissions/203b9ff2-166d-418b-99a6-4fa5268fb1e6

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
theorem _root_.solution (b : B) : Monotone (fun t => R.rank b (R.state t b)) := by
  classical
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  by_cases h : b ∈ R.support i
  · exact (R.HWORSE i b h).le
  · rw [R.HOUT i b h]
end F6SmallBlockTokenCapacity.TokenRun
