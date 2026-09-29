-- Prove2me | solution 1 for Freiman.middleRepair_row_regular_proper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:50:44.226972+00:00
-- url     : https://prove2.me/submissions/dd97e13d-c911-4459-89fd-b2499a298bbd

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.NormNum

open Freiman

theorem solution :
    (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v → 0<u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) →
    ∀ (c : MiddleCore) (r : MiddleRow), middleRegular c → ∀ d ∈ middleRepairRowChildren c r, middleRegular d ∧ middleRepairProper c d := by
  intro child c r hc d hd
  have child' (u v : List ℕ+) (hu : middleDigits123 u) (hv : middleDigits123 v)
      (hpos : 0 < u.length + v.length) := child c u v hc hu hv hpos
  cases r <;>
    simp only [middleRepairRowChildren, middleRepairJ, List.replicate_succ,
      List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hd <;>
    rcases hd with rfl | rfl | rfl | rfl <;>
    apply child' <;> norm_num [middleDigits123]

#print axioms solution
