-- Prove2me | solution 1 for Erdos266.mseq_dOf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:47:58.943642+00:00
-- url     : https://prove2.me/submissions/995b21f6-f5df-4b82-85de-8abca6cc2ea0

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : mseq (dOf k) ≤ k :=
  Nat.findGreatest_spec (P := fun d => mseq d ≤ k) (Nat.zero_le k) hk
end Erdos266
