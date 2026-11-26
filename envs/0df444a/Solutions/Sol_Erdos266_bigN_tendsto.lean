-- Prove2me | solution 1 for Erdos266.bigN_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:05:02.69604+00:00
-- url     : https://prove2.me/submissions/97c94cb4-9f26-417e-930d-4636aec2c74c

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_le_bigN

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution : Tendsto (fun k => (bigN k : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast le_bigN k
end Erdos266
