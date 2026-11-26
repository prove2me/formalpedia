-- Prove2me | solution 1 for FixedOrderFactor.summable_fN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:15.640669+00:00
-- url     : https://prove2.me/submissions/f1265ef2-eaac-467d-93f0-4a752b9d000f

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Euler
public import Theorems.Thm_FixedOrderFactor_fN_apply

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (N : Finset Nat.Primes) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n => ‖fN N s (by omega) n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))
  rw [fN_apply]; split_ifs <;> simp
end FixedOrderFactor
