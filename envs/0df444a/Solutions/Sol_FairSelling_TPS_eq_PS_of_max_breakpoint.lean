-- Prove2me | solution 1 for FairSelling.TPS_eq_PS_of_max_breakpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:17.188028+00:00
-- url     : https://prove2.me/submissions/78532486-67e2-44df-92fc-ef63148e44fa

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_TPS_eq_PS_of_top
import Theorems.Thm_FairSelling_vval_mem_breakpoints

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {a : ℝ}
    (hmax : ∀ s ∈ breakpoints v p, s ≤ a) (hfa : a ≤ truncSum n v p a) :
    TPS n v p = PS n v p :=
  TPS_eq_PS_of_top v p hp (fun g => hmax _ (vval_mem_breakpoints v p g)) hfa
end FairSelling
