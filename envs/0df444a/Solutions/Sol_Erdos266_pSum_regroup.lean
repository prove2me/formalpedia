-- Prove2me | solution 1 for Erdos266.pSum_regroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:16.159798+00:00
-- url     : https://prove2.me/submissions/8c2e8396-8527-4412-82e0-b13b79a57827

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_partial_regroup

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (i' k : ℕ) : pSum i' (cnt k) = finSum i' k Sinf :=
  partial_regroup i' k
end Erdos266
