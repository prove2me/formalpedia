-- Prove2me | solution 1 for FixedOrderFactor.sqrtCount_eq_card_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:17.534303+00:00
-- url     : https://prove2.me/submissions/26631198-f68e-4a01-b78e-1bfc03252559

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sqrtCount_eq_card_zmod__2e6db6efff87


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {M : ℕ} [NeZero M] {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    sqrtCount M a s = (Finset.univ.filter fun y : ZMod M =>
      IsUnit y ∧ y ^ 2 = a ∧ ZMod.castHom hs (ZMod s) y = -1).card :=
  sqrtCount_eq_card_zmod' hs a
end FixedOrderFactor
