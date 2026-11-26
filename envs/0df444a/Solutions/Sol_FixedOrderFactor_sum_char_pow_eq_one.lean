-- Prove2me | solution 1 for FixedOrderFactor.sum_char_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:09:52.053332+00:00
-- url     : https://prove2.me/submissions/22d8b3f5-6dd9-4507-a43e-1e30a9f33f79

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_char_pow_eq_one__fb05deb8e53f


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical
namespace FixedOrderFactor
theorem _root_.solution (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1) (a b : ZMod p)
    (hb : b ≠ 0) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1),
        χ a * starRingEnd ℂ (χ b) =
      if ∃ c : ZMod p, c ≠ 0 ∧ a = c ^ r * b then (r : ℂ) else 0 :=
  sum_char_pow_eq_one' p hr a b hb
end FixedOrderFactor
