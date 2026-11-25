-- Prove2me | solution 1 for Erdos1063.valuation_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:43:07.19691+00:00
-- url     : https://prove2.me/submissions/d474f445-72fe-45a6-9753-418e6a8bec28

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower
public import Theorems.Thm_Erdos1063_valuation_bound_aux

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) :=
  (valuation_bound_aux hp hkn hpk hk hgood).2
end Erdos1063
