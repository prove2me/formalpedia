-- Prove2me | solution 1 for FixedOrderFactor.tendsto_muAvg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:07:59.905664+00:00
-- url     : https://prove2.me/submissions/227db55f-7fef-4f18-ad86-ab2d25f1eb83

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_tendsto_muAvg__0f3103de6ec7


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) :=
  tendsto_muAvg' hx
end FixedOrderFactor
