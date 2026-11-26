-- Prove2me | solution 1 for FixedOrderFactor.one_sub_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:52:08.678901+00:00
-- url     : https://prove2.me/submissions/9c5632c1-c96d-4a0e-a64a-2019fc4cb2fd

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_pow_r

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (j : ℕ) {x : ℂ} (hx : x ^ r ≠ 1) :
    1 - rootOfUnity r j * x ≠ 0 := by
  intro h
  apply hx
  have h1 : rootOfUnity r j * x = 1 := by linear_combination -h
  have := congrArg (· ^ r) h1
  simpa [mul_pow, rootOfUnity_pow_r hr] using this
end FixedOrderFactor
