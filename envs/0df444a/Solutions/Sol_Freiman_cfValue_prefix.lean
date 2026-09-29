-- Prove2me | solution 1 for Freiman.cfValue_prefix
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:42:59.539048+00:00
-- url     : https://prove2.me/submissions/33a468a4-791c-40ff-9aaa-b8fcd1833982

import Definitions.Def_Freiman_prefixEval
import Theorems.Thm_Freiman_cf_convergence

open Freiman

set_option autoImplicit false

theorem solution (b : ℕ → ℕ+) (m : ℕ) :
    cfValue b = prefixEval ((List.range m).map b)
      (cfValue (fun k => b (m + k))) := by
  induction m generalizing b with
  | zero => simp [prefixEval]
  | succ m ih =>
    rw [(cf_convergence b).2.2.2.2]
    rw [ih (fun n => b (n + 1))]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, prefixEval]
    simp only [Function.comp_def, Nat.succ_eq_add_one,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
