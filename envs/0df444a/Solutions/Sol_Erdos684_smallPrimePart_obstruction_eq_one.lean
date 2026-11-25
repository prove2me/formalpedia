-- Prove2me | solution 1 for Erdos684.smallPrimePart_obstruction_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:12:08.990485+00:00
-- url     : https://prove2.me/submissions/da9f2d59-7004-435c-8193-1015fb014dfd

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower
public import Theorems.Thm_Erdos684_obstructionModulus_pos
public import Theorems.Thm_Erdos684_prime_power_dvd_obstructionModulus
public import Theorems.Thm_Erdos684_smallPrimePart_pred_eq_one


set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684
namespace Erdos684
theorem _root_.solution (K : ℕ) {k : ℕ} (hk : k ≤ K) :
    smallPrimePart (obstructionModulus K - 1) k = 1 := by
  apply smallPrimePart_pred_eq_one (obstructionModulus_pos K) _ hk
  intro p hp hpk
  refine ⟨Nat.log p K + 1, ?_, prime_power_dvd_obstructionModulus hp hpk⟩
  exact Nat.lt_pow_succ_log_self hp.one_lt K
end Erdos684
