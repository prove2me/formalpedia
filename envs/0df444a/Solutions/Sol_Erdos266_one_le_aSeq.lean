-- Prove2me | solution 1 for Erdos266.one_le_aSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:24.316425+00:00
-- url     : https://prove2.me/submissions/0717146f-5234-4261-ba07-80f49fd5bf1a

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_jOf_lt
public import Theorems.Thm_Erdos266_elemZ_pos
public import Theorems.Thm_Erdos266_aSeq_cast

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (n : ℕ) : 1 ≤ aSeq n := by
  have h1 := elemZ_pos (jOf_lt n)
  have h2 := aSeq_cast n
  omega
end Erdos266
