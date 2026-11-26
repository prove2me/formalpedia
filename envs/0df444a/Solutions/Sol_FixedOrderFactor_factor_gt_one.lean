-- Prove2me | solution 1 for FixedOrderFactor.factor_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:56:24.910792+00:00
-- url     : https://prove2.me/submissions/4a54b578-cf3b-46cc-88af-083baa083028

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order

set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 1 < (1 + y) / (1 - y) := by
  rw [lt_div_iff₀ (by linarith)]; linarith
end FixedOrderFactor
