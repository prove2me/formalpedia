-- Prove2me | solution 2 for BookProof.BRSTNilpotent.chi_cyc3
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T15:17:14.614817+00:00
-- url     : https://prove2.me/submissions/c4f03eaa-d21e-4316-bc08-34c94853c408

-- Generated from ChapterBRSTNilpotent.lean — solution of BookProof.BRSTNilpotent.chi_cyc3
import Mathlib
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent













variable {R : Type*} [Ring R] [Algebra ℝ R]
variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (χ β : Fin n → R) (hCAR : GhostCAR χ β) (a b c : Fin n) :
    χ a * χ b * χ c = χ b * χ c * χ a := by

  have h1 : χ a * χ b = - (χ b * χ a) := by
    exact eq_neg_of_add_eq_zero_left ( hCAR.chichi a b )
  have h2 : χ a * χ c = - (χ c * χ a) := by
    exact eq_neg_of_add_eq_zero_left ( hCAR.chichi a c );
  simp [ mul_assoc, h1, h2 ]
