-- Prove2me | solution 1 for Freiman.middleRepair_j_regular_proper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:55:49.358125+00:00
-- url     : https://prove2.me/submissions/3f6ca2ab-5397-4502-8e12-dc5241823446

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v → 0<u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) →
    ∀ (c : MiddleCore) (k : ℕ), middleRegular c → 1 ≤ k → middleRegular (middleRepairJ c k) ∧ middleRepairProper c (middleRepairJ c k) := by
  intro h c k hc hk
  apply h c (List.replicate k 3) (List.replicate k 3) hc
  · intro a ha
    have ha3 : a = 3 := (List.mem_replicate.mp ha).2
    subst a
    norm_num
  · intro a ha
    have ha3 : a = 3 := (List.mem_replicate.mp ha).2
    subst a
    norm_num
  · simp only [List.length_replicate]
    omega

#print axioms solution
