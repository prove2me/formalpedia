-- Prove2me | solution 1 for FixedOrderFactor.castHom_natCast_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:28.857806+00:00
-- url     : https://prove2.me/submissions/ad00ad21-ef28-44ee-b118-e28105cb5938

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]
omit [NeZero M]
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : s ∣ M) (x : ℕ) :
    ZMod.castHom hs (ZMod s) (x : ZMod M) = -1 ↔ s ∣ x + 1 := by
  rw [map_natCast, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one,
    eq_neg_iff_add_eq_zero]
end FixedOrderFactor
