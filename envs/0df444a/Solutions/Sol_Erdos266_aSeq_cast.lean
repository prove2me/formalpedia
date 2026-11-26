-- Prove2me | solution 1 for Erdos266.aSeq_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:14.213518+00:00
-- url     : https://prove2.me/submissions/dbd50d6c-4333-47d6-a4d0-fb36d8a36398

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_jOf_lt
public import Theorems.Thm_Erdos266_elemZ_pos

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (n : ℕ) : (aSeq n : ℤ) = elemZ (kOf n) (n - cnt (kOf n)) :=
  Int.toNat_of_nonneg (elemZ_pos (jOf_lt n)).le
end Erdos266
