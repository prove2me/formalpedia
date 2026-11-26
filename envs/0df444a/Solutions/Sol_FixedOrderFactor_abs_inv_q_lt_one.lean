-- Prove2me | solution 1 for FixedOrderFactor.abs_inv_q_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:21.764673+00:00
-- url     : https://prove2.me/submissions/455f1f9c-1150-4191-a703-1bc01bf6b94e

module
public import Definitions.Def_FixedOrderFactor_Euler
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Model
public import Theorems.Thm_FixedOrderFactor_inv_q_lt_one
public import Theorems.Thm_FixedOrderFactor_inv_q_pos


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (q : Nat.Primes) : |1 / (q : ℝ)| < 1 := by
  rw [abs_of_pos (inv_q_pos q)]; exact inv_q_lt_one q
end FixedOrderFactor
