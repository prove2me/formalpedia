-- Prove2me | solution 1 for Erdos266.le_dOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:50:42.156551+00:00
-- url     : https://prove2.me/submissions/a6c446f0-4934-4b98-b045-ce4c5c65a082

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_add_two_le_mseq

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {d k : ℕ} (hm : mseq d ≤ k) : d ≤ dOf k := by
  refine Nat.le_findGreatest ?_ hm
  have := add_two_le_mseq d
  omega
end Erdos266
