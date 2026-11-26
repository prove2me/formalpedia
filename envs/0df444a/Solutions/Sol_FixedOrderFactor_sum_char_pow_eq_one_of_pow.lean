-- Prove2me | solution 1 for FixedOrderFactor.sum_char_pow_eq_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:10:06.809958+00:00
-- url     : https://prove2.me/submissions/b1d55b45-901b-4bb2-9800-f33e587ea8b4

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_char_pow_eq_one_of_pow__9a04af0fa11c


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical
namespace FixedOrderFactor
theorem _root_.solution (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1)
    {m n d a b : ℕ} (hm : m = d * a ^ r) (hn : n = d * b ^ r) (hpm : ¬ p ∣ m) (hpn : ¬ p ∣ n) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ m * starRingEnd ℂ (χ n) = r :=
  sum_char_pow_eq_one_of_pow' p hr hm hn hpm hpn
end FixedOrderFactor
