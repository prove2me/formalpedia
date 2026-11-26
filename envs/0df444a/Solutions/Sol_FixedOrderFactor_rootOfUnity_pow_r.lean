-- Prove2me | solution 1 for FixedOrderFactor.rootOfUnity_pow_r
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:50:32.750017+00:00
-- url     : https://prove2.me/submissions/308b39a2-1974-4955-a3c8-33b6040eca99

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_eq

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (j : ℕ) : rootOfUnity r j ^ r = 1 := by
  rw [rootOfUnity_eq, ← pow_mul, mul_comm j r, pow_mul,
    (Complex.isPrimitiveRoot_exp r hr.ne').pow_eq_one, one_pow]
end FixedOrderFactor
