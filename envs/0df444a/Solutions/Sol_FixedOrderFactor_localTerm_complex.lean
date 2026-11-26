-- Prove2me | solution 1 for FixedOrderFactor.localTerm_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:11.882465+00:00
-- url     : https://prove2.me/submissions/d66fe044-91c4-4259-9905-e41d91246e0c

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (z : ℂ) (_hz : (starRingEnd ℂ) z * z = 1) (x : ℝ) :
    (localTerm z x : ℂ) = 1 / ((1 - z * x) * (1 - (starRingEnd ℂ) z * x)) := by
  rw [localTerm, Complex.ofReal_div, Complex.ofReal_one, ← Complex.mul_conj]
  simp [map_sub, Complex.conj_ofReal]
end FixedOrderFactor
