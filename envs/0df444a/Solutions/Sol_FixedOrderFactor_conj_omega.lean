-- Prove2me | solution 1 for FixedOrderFactor.conj_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:34.388896+00:00
-- url     : https://prove2.me/submissions/3407fe41-dcbd-414d-a854-c1c33035ca70

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (r : ℕ) : starRingEnd ℂ (ω r) = (ω r)⁻¹ := by
  rw [ω, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring
end FixedOrderFactor
