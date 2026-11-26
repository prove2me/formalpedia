-- Prove2me | solution 1 for FixedOrderFactor.card_char_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:10:00.847607+00:00
-- url     : https://prove2.me/submissions/f5fcff8f-1f22-4375-9af8-62239b95a6a3

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_card_char_pow_eq_one__ac5283578e4c


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical
namespace FixedOrderFactor
theorem _root_.solution (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : r ∣ p - 1) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter (fun χ => χ ^ r = 1)).card = r :=
  card_char_pow_eq_one' p hr
end FixedOrderFactor
