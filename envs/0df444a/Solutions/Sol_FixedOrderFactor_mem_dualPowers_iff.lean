-- Prove2me | solution 1 for FixedOrderFactor.mem_dualPowers_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:53:56.007806+00:00
-- url     : https://prove2.me/submissions/5896345a-1296-4c30-9b7f-deeaa8e7f39a

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters

set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) (χ : MulChar (ZMod p) ℂ) :
    χ ∈ dualPowers p r ↔ χ ^ r = 1 := by
  rw [MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
  constructor
  · intro h
    ext u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val]
    exact h _ ⟨u, rfl⟩
  · rintro h _ ⟨u, rfl⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow, ← MulChar.pow_apply_coe, h,
      MulChar.one_apply_coe]
end FixedOrderFactor
