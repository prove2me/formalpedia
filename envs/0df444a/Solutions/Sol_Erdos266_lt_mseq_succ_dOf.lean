-- Prove2me | solution 1 for Erdos266.lt_mseq_succ_dOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:52:27.140797+00:00
-- url     : https://prove2.me/submissions/fc25b175-850c-46ec-a344-89e07bd808cd

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_le_dOf

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} : k < mseq (dOf k + 1) := by
  by_contra h
  push Not at h
  have h1 : dOf k + 1 ≤ dOf k := le_dOf h
  omega
end Erdos266
