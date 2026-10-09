-- Prove2me | solution 1 for BookProof.Complexification.Cx.ofReal_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:49:49.177206+00:00
-- url     : https://prove2.me/submissions/55962e1d-3fdb-43ac-9757-1917c4c1e6f3

-- Generated from Complexification.lean — solution of BookProof.Complexification.Cx.ofReal_add
import Mathlib
import Definitions.Def_Complexification
open BookProof.Complexification
open BookProof.Complexification.Cx



open scoped RealInnerProductSpace
open RCLike


set_option linter.unusedSectionVars false

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

set_option maxHeartbeats 1000000 in
theorem solution (a b : W) : ofReal (a + b) = ofReal a + ofReal b := by
 ext <;> simp
