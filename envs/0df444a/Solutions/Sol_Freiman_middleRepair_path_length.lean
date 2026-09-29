-- Prove2me | solution 1 for Freiman.middleRepair_path_length
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:50:23.454392+00:00
-- url     : https://prove2.me/submissions/1229dccd-aaad-4532-aa46-eb0b0a42d727

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.SplitIfs

open Freiman

private theorem length_normalized (c : MiddleCore) :
    (middleNormalized c).left.length + (middleNormalized c).right.length =
      c.left.length + c.right.length := by
  unfold middleNormalized
  split_ifs <;> simp_all [Nat.add_comm]

private theorem length_child (c : MiddleCore) (u v : List ℕ+) :
    (middleRepairChild c u v).left.length + (middleRepairChild c u v).right.length =
      c.left.length + c.right.length + u.length + v.length := by
  rw [middleRepairChild, length_normalized]
  simp only [middleRepairRawChild, List.length_append]
  have h := length_normalized c
  omega

theorem solution :
    ∀ (c : MiddleCore) (t : ℝ) (p : ℕ→MiddleCore), middleRepairPath c t p →
      ∀ n : ℕ, n+c.left.length+c.right.length ≤ (p n).left.length+(p n).right.length := by
  intro c t p hp n
  induction n with
  | zero =>
    rw [hp.1, length_normalized]
    omega
  | succ n ih =>
    obtain ⟨u, v, _, _, hpos, heq⟩ := (hp.2 n).2.2.2
    rw [heq, length_child]
    omega

#print axioms solution
