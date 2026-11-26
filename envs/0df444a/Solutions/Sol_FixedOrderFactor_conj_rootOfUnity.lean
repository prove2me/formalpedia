-- Prove2me | solution 1 for FixedOrderFactor.conj_rootOfUnity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:08.92311+00:00
-- url     : https://prove2.me/submissions/8185fd95-7253-45b5-b7ed-8650720b0676

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r j : ℕ) : (starRingEnd ℂ) (rootOfUnity r j) * rootOfUnity r j = 1 := by
  rw [rootOfUnity, ← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring
end FixedOrderFactor
