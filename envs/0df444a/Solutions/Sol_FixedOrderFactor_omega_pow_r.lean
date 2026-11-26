-- Prove2me | solution 1 for FixedOrderFactor.omega_pow_r
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:17.457875+00:00
-- url     : https://prove2.me/submissions/ac7bc205-5479-4cd0-83ac-b09ac19f5424

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
theorem _root_.solution {r : ℕ} (hr : 0 < r) : ω r ^ r = 1 :=
  (Complex.isPrimitiveRoot_exp r hr.ne').pow_eq_one
end FixedOrderFactor
