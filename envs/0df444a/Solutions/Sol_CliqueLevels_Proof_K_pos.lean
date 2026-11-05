-- Prove2me | solution 1 for CliqueLevels.Proof.K_pos
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:43:27.830576+00:00
-- url     : https://prove2.me/submissions/836f4ffb-457d-4e1a-9b5d-7c14bb91276c

import Definitions.Def_LevelsStatement
import Mathlib.Tactic.NormNum
set_option autoImplicit false

theorem solution (x₀ l : ℕ) : 0 < Levels.Gen.K x₀ l := by
  cases l with
  | zero => exact Nat.two_pow_pos x₀
  | succ l => exact pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (solution x₀ l)) 2
