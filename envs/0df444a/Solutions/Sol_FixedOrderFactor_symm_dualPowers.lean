-- Prove2me | solution 1 for FixedOrderFactor.symm_dualPowers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:58.503965+00:00
-- url     : https://prove2.me/submissions/be89ba56-f905-4a9f-8b32-1a9101b3f008

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
theorem _root_.solution (r : ℕ) :
    (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ).symm (OrderDual.toDual (dualPowers p r))
      = powers p r := by
  simp [dualPowers]
end FixedOrderFactor
