-- Prove2me | solution 1 for FixedOrderFactor.muAvg_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:44.794424+00:00
-- url     : https://prove2.me/submissions/e57a42e1-2e5a-46db-9b2a-d62a92fe0768

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_muAvg_eq__11fccbbf11a9


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) {x : ℝ} (hx : |x| < 1) :
    muAvg r x = (1 + x ^ r) / ((1 - x ^ 2) * (1 - x ^ r)) :=
  muAvg_eq' hr hx
end FixedOrderFactor
