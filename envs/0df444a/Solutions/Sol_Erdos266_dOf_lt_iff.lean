-- Prove2me | solution 1 for Erdos266.dOf_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:52:24.804803+00:00
-- url     : https://prove2.me/submissions/a16384ea-157b-4be6-a99b-181202f8d2e1

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
public import Theorems.Thm_Erdos266_mseq_strictMono
public import Theorems.Thm_Erdos266_mseq_dOf_le
public import Theorems.Thm_Erdos266_le_dOf

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {d k : ℕ} (hk : 2 ≤ k) : dOf k < d ↔ k < mseq d := by
  constructor
  · intro h
    by_contra h2
    push Not at h2
    exact absurd (le_dOf h2) (by omega)
  · intro h
    by_contra h2
    push Not at h2
    have h3 : mseq d ≤ mseq (dOf k) := mseq_strictMono.monotone h2
    have h4 := mseq_dOf_le hk
    omega
end Erdos266
